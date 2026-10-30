-- Prove2me | Theorems.Thm_JailletLu_third_ge_R
-- name    : JailletLu.third_ge_R
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:32:51.908253+00:00
-- url     : https://prove2.me/theorems/863b577b-af8a-4d3a-a50c-bcb21e0d9e75
-- title:
--   §5.4: the third-line ratio is at least $R(f_a,\beta_a,s_a)$
-- statement:
--   **Setting.** Let $A$ (advertisers) and $I$ (impression types) be finite sets, $E\subseteq A\times I$ the edges of the bipartite graph ($a\sim i$ when $(a,i)\in E$), $r_i\le 1$ the arrival rate of type $i$ (the standing assumption of §5), and $n$ the number of requests. Let $f=(f_{a,i})$ be a feasible point of LP (4), extended by the dummy advertiser $a_d$ with $f_{a_d,i}=r_i-\sum_{a}f_{a,i}$ and the convention $f_{a_d}=1$, and write $f_a=\sum_{i\sim a}f_{a,i}$. Fix, for every type $i$, any order $a_1,\dots,a_k$ of the advertisers interested in $i$ (the dummy included). The list numbers $m^i_{b,c}$ and $m_{b,c}=\sum_i m^i_{b,c}$ ($b,c\in A^*=A\cup\{a_d\}$) are those of the §5.3 construction, and for $a\in A$: $A^*_a=A^*\setminus\{a\}$, $\beta_a=\max_{a_1\in A^*_a}m_{a,a_1}$, $s_a=\sum_{a_1\in A^*_a}m_{a,a_1}$.
--
--   Then for every advertiser $a\in A$ with $f_a>0$,
--   $$
--   \frac1{f_a}\Big(1-e^{-f_a}+\frac1e\sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})-\frac1{2e}\Big(\sum_{a_1\in A^*_a}g(f_{a_1},m_{a_1,a})\Big)^2+\frac1{2e}\sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})^2\Big)\ \ge\ R(f_a,\beta_a,s_a).
--   $$
--   This reduces the per-advertiser ratio, which depends on the whole list structure, to a function of three numbers, so that Claim 4 can finish the bound.
--
--   Differences from the source:
--   - reading: the order a_1, …, a_k of the advertisers interested in i is not fixed → every admissible order: a duplicate-free list of exactly the interested advertisers, dummy included; reason: the paper fixes no order; the statement holds for every one
--   - reading: x ± r_i/2 ∈ [Σ_{l<k} f_{a_l,i}, Σ_{l≤k} f_{a_l,i}] → rot(x) = x + r_i/2 if x < r_i/2, else x − r_i/2, with closed intervals; reason: for x ∈ [0, r_i] this is the one of x ± r_i/2 lying in [0, r_i] (both only at x = r_i/2); interval endpoints have measure 0
--   - encoding: m^i_{b,c}, the expected number of requests of type i whose list is ⟨b, c⟩ → Lebesgue measure of {x ∈ [0, r_i] : x ∈ J_i(b), rot(x) ∈ J_i(c)}; reason: n requests, type i with probability r_i/n, x uniform on [0, r_i]: n · (r_i/n) · |·|/r_i = |·|; same values, the probability space is not built
--   - generalization: f the solution of LP (4) used by the algorithm, with Σ_i r_i = n → f any feasible point of LP (4); Σ_i r_i = n not assumed; reason: optimality and the normalization are never used; the paper's f is feasible, so the statement specializes to it
--   - encoding: the quotients by f_a → hypothesis f_a > 0; reason: the printed quotients are defined only there
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, last display (unnumbered)

import Mathlib
import Definitions.Def_JailletLu_LP4Feasible
import Definitions.Def_JailletLu_IsAdmissibleOrder
import Definitions.Def_JailletLu_fTot
import Definitions.Def_JailletLu_beta
import Definitions.Def_JailletLu_sA
import Definitions.Def_JailletLu_R
import Definitions.Def_JailletLu_third

namespace JailletLu

/-- **Reduction of the third line to `R`** (unnumbered).
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, last display: "Therefore, (1/f_a)(1 − e^{−f_a} + (1/e) Σ_{a1∈A*_a} g(f_a, m_{a,a1})
− (1/(2e))(Σ_{a1∈A*_a} g(f_{a1}, m_{a1,a}))² + (1/(2e)) Σ_{a1∈A*_a} g(f_a, m_{a,a1})²) ≥ (1/f_a)(1 −
e^{−f_a} + (1/e)(s_a/β_a) g(f_a, β_a) − (1/(2e))(e^{−1}(s_a − β_a) + g(1, β_a))² + (1/(2e))
g(f_a, β_a)²) ≜ R(f_a, β_a, s_a)."

Setting (§5, p. 12 and §5.3, p. 13): `r_i ≤ 1` for every type (the standing assumption of §5), `f`
feasible for LP (4) with parameter `n`, and an admissible order of the interested advertisers for
every type (any order: the paper fixes none). The list numbers are those of the §5.3 construction.
Conclusion, for every advertiser `a` with `f_a > 0`: `third_a / f_a ≥ R(f_a, β_a, s_a)`, where
`third_a` is the bracket of the third line (`JailletLu.third`).

**Formalization Note.** `f_a > 0` is where the paper's quotients are defined. -/
theorem third_ge_R {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]
    (E : Set (A × I)) (r : I → ℝ) (hr : ∀ i, r i ≤ 1) (n : ℕ) (f : A → I → ℝ)
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (hord : IsAdmissibleOrder E ord) (a : A) (ha : 0 < fTot f a) :
    R (fTot f a) (beta r f ord a) (sA r f ord a) ≤ third r f ord a / fTot f a := by sorry

end JailletLu
