-- Prove2me | Theorems.Thm_IterRoundDet_Supplement_theorem_1_3
-- name    : IterRoundDet.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:05:45.342334+00:00
-- url     : https://prove2.me/theorems/9742058e-22b8-433e-bad3-47a9f5ad9605
-- title:
--   Theorem 1.3 — a deterministic polynomial-time algorithm finds a base of $\mathcal M$ within $e^{15d+\varepsilon}$ of the maximum of $p_{\mathcal N,w}$
-- statement:
--   Let $\mathcal N$ be a matroid on $[n]$ of rank $d$, $\mathcal M$ a matroid on $[n]$ of rank $r\ge d$, and $w\in\mathbb Q^n_{>0}$ positive weights, and let $p_{\mathcal N,w}(z)=\sum_{I\in\mathcal B(\mathcal N)}w^Iz^I$ be the weighted matroid basis polynomial of $\mathcal N$. There is a deterministic polynomial-time algorithm that, given $\mathcal N$ and $\mathcal M$ by independence oracles, the weights $w$, and $\varepsilon>0$, returns a base $B\in\mathcal B(\mathcal M)$ with
--
--   $$\log p_{\mathcal N,w}(\mathbf 1_B)\;\ge\;\max_{B^*\in\mathcal B(\mathcal M)}\log p_{\mathcal N,w}(\mathbf 1_{B^*})-15d-\varepsilon .$$
--
--   Precisely: there are one coin-free program $P$ and constants $C,K$ such that for every instance $(n,d,b,\mathcal N,\mathcal M,w,\varepsilon)$, where $b$ bounds the bit length of every weight's numerator and denominator, the run of $P$ on input $[n,d,b,\lceil 1/\varepsilon\rceil]$ followed by the weights, with the two independence oracles, halts within log-cost time $T=C(2+n+b+\lceil1/\varepsilon\rceil)^K$ (oracle answers charged) and outputs the characteristic word of a base $B$ of $\mathcal M$ satisfying
--
--   $$e^{-15d-\varepsilon}\,p_{\mathcal N,w}(\mathbf 1_{B^*})\le p_{\mathcal N,w}(\mathbf 1_B)\qquad\text{for every base }B^*\text{ of }\mathcal M .$$
--
--   The polynomial $p_{\mathcal N,w}$ is completely log-concave but in general not real stable, so this result is not a case of Theorem 1.1; its loss is $15d$ rather than $14d$, the extra $d$ coming from a marginal-entropy proxy for the maximum-entropy functional. For $d=r$ it gives a $e^{15d+\varepsilon}$-approximation, on the multiplicative scale, for a product-weighted common-base counting problem of two matroids.
--
--   **Formalization Note** The machine, its log-cost charging, the set and rational encodings and the reading of "polynomial time" are those of the base mission's Theorem 1.1 (value clause): $P$, $C$, $K$ are fixed before the instance and before $\varepsilon$. The conclusion is in multiplicative form, which is the printed inequality under the convention $\log 0=-\infty$; Lean's $\log 0=0$ would distort the logarithmic form when some value is $0$.
--
--   Differences from the source:
--   - reading: weights $w\in\mathbb R^n_{>0}$ → positive rationals $w\in\mathbb Q^n_{>0}$ written on the input with a bit bound $b$; reason: an algorithm can only read finitely encoded weights, and the paper's proof (§5.1, p.24) fixes "positive rational weights"; polynomial time is measured in $n$, $b$ and $\lceil1/\varepsilon\rceil$.
--   - reading: "given a matroid $\mathcal N$ …, a matroid $\mathcal M$" → both matroids through independence oracles, both on the whole ground set $[n]$; reason: the theorem names no access model, and the independence oracle is the one Theorem 1.1 uses for $\mathcal M$ and for the support matroid.
--   - encoding: $\log p(\mathbf 1_B)\ge\max_{B^*}\log p(\mathbf 1_{B^*})-15d-\varepsilon$ → $e^{-15d-\varepsilon}p(\mathbf 1_{B^*})\le p(\mathbf 1_B)$ for every base $B^*$; reason: equivalent under $\log 0=-\infty$, and avoids Lean's $\log 0=0$.
--   - encoding: "deterministic polynomial-time algorithm" → one coin-free program with a time bound $C(2+n+b+\lceil1/\varepsilon\rceil)^K$ on the base mission's log-cost oracle machine; reason: the base mission's cost model, unchanged.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 1.3, p.3 (PDF p.4); proof in §5.1, pp.24–27 (PDF pp.25–28)

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Machine
import Definitions.Def_IterRoundDet_Oracles
import Definitions.Def_IterRoundDet_Supplement_BasisPoly

set_option autoImplicit false

namespace IterRoundDet.Supplement

open IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 1.3 (Matroid
basis-polynomial maximization), p.3 (PDF p.4); proved in §5.1, pp.24–27. There is a deterministic
polynomial-time algorithm that, given a matroid `N` on `[n]` of rank `d`, a matroid `M` on `[n]` of rank
`r ≥ d`, weights `w ∈ ℝ^n_{>0}`, and `ε > 0`, returns a base `B ∈ B(M)` such that
`log p_{N,w}(1_B) ≥ max_{B*∈B(M)} log p_{N,w}(1_{B*}) − 15d − ε`.

**Formalization Note.** The cost model is that of `IterRoundDet.theorem_1_1`, clause (a): one coin-free
program `P` and one pair `C, K`, chosen before the instance and before `ε`; log-cost time on the machine
of `IterRoundDet.Machine` with oracle answers charged, bounded by `C·(2 + n + b + N)^K` with
`N = ⌈1/ε⌉₊`. `N` and `M` are given by independence oracles (`basisModel`, tags `1` and `0`); the input
is `[n, d, b, N]` followed by the weights (`ratList w`); `b` bounds the bit length of every weight's
numerator and denominator. The weights are positive rationals (§5.1). The conclusion is multiplicative,
`e^{−15d−ε} p(1_{B*}) ≤ p(1_B)` for every base `B*` of `M`, which is the printed line under the
convention `log 0 = −∞` (`Real.log 0 = 0` would corrupt the log form). -/
theorem theorem_1_3 :
    ∃ (P : Program) (C K : ℕ), CoinFree P ∧
      ∀ (n d b : ℕ) (N M : Matroid (Fin n)) (w : Fin n → ℚ) (ε : ℝ),
        N.E = Set.univ → N.eRank = d → M.E = Set.univ → (d : ℕ∞) ≤ M.eRank →
        (∀ i, 0 < w i) → WeightBits b w → 0 < ε →
        let Nε := ⌈1 / ε⌉₊
        let T := C * (2 + n + b + Nε) ^ K
        let s := run P (basisModel M N) ([n, d, b, Nε] ++ ratList w) (fun _ => false) T
        s.out.isSome ∧ s.cost ≤ T ∧ ∃ B : Finset (Fin n), s.out = some (setCode B) ∧
          M.IsBase (B : Set (Fin n)) ∧
          ∀ B' : Finset (Fin n), M.IsBase (B' : Set (Fin n)) →
            Real.exp (-(15 * d) - ε) * pEval (castCoef (basisCoef N w)) (ind B') ≤
              pEval (castCoef (basisCoef N w)) (ind B) := by sorry

end IterRoundDet.Supplement
