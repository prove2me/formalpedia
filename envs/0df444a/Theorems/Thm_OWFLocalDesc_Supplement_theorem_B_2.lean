-- Prove2me | Theorems.Thm_OWFLocalDesc_Supplement_theorem_B_2
-- name    : OWFLocalDesc.Supplement.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T17:02:03.646589+00:00
-- url     : https://prove2.me/theorems/1d121147-4562-4a24-bde0-b3279e5c7466
-- title:
--   Theorem B.2 — global descriptions are never much longer than pointwise ones, and the cyclic labeling separates them
-- statement:
--   Fix polynomial schedules $m(n)\ge1$ and $t(n)\ge1$, a pointwise decoder $U$ and a global decoder $V$. Then there are a polynomial global clock $T(n)\ge1$ and constants $c,c_{\mathrm{cyc}}\in\mathbb N$ such that the following hold for every point length $n\ge1$ and every $0<\theta\le1$.
--
--   1. For every dataset $(x,y)$,
--   $$\mathrm{pK}^T_{\mathrm{all},\theta}(y\mid E(x))\ \le\ \mathrm{pSC}^t_\theta(x,y)+c$$
--   in $\mathbb N\cup\{\infty\}$.
--   2. Let $Y=Y(X)$ be the cyclic first-bit labeling of the point vector $X$ ($Y_i$ is the first bit of $X_{i+1}$, and $Y_m$ that of $X_1$). Then $\mathrm{pK}^T_{\mathrm{all},\theta}(Y\mid E(X))\le c_{\mathrm{cyc}}$ for every point vector $X$.
--   3. For $X$ uniform on $(\{0,1\}^n)^{m}$ and every integer $s\ge0$,
--   $$\Pr_X\big[\mathrm{pSC}^t_\theta(X,Y)\le s\big]\ \le\ \frac{2^{2s+2-m}}{\theta}.$$
--   4. If $\varepsilon_n=\binom{m}{2}2^{-n}<1$, then for every integer $s\ge0$ the same probability conditioned on the points being distinct is at most
--   $$\frac{2^{2s+2-m}}{\theta(1-\varepsilon_n)}.$$
--
--   A program that sees the whole point vector is never much worse than a local certificate. The cyclic labeling has constant global price, but by item 3 at $s=\lfloor m/3\rfloor$ its pointwise quantile exceeds $\lfloor m/3\rfloor$ except with probability at most $4\theta^{-1}2^{-m/3}$.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - generalization: the global decoder V, one efficiently universal machine fixed once and for all (Appendix B, p.37) → every `GlobalDecoder`: any step-indexed machine with the clock, sequential-reading and universality properties stated on p.37; reason: the paper's V has these properties, so the statement specializes to it
--   - encoding: Pr_X over independent uniform points; the conditional probability given distinct points → count of point vectors over 2^{m(n)n}; ratio of counts over injective point vectors; reason: the uniform measure and the conditional measure on the distinctness event; no instance changes
--   - encoding: pK^T_{all,θ}(y|E(x)) ≤ pSC^t_θ(x,y) + c in the extended nonnegative integers; 2^{2s+2−m} → inequality in ℕ∞ (⊤ + c = ⊤); `zpow` with integer exponent 2s+2−m(n); reason: same values
--   - encoding: every dataset; points of length n (positive) → ∀ n ≥ 1, every x : Fin (m n) → Fin n → Bool and y; reason: point lengths are positive throughout (§2, p.11); the first bit and enc(n) need n ≥ 1
--   - encoding: a polynomial clock T(n) (a positive integer-valued function, Definition B.1) → `QuantumPRC.EffPoly` T with T n ≥ 1; reason: the paper's polynomial global clock
--   - encoding: polynomial schedules m(n) ≥ 1, t(n) ≥ 1 → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable, exactly the paper's polynomial schedules
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem B.2, p.38 (restatement of Theorem 1.8)

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_pSC
import Definitions.Def_OWFLocalDesc_Supplement_pKT
import Definitions.Def_OWFLocalDesc_Supplement_cyclicLabels
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

open OWFLocalDesc

/-- **Theorem B.2 (Global and pointwise reconstruction; restatement of Theorem 1.8).**
Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Theorem B.2, p.38: "Fix polynomial schedules m(n) ≥ 1
and t(n) ≥ 1, the pointwise decoder U, and the global decoder V. There are a polynomial clock T(n)
and constants c, c_cyc such that, for every dataset and every 0 < θ ≤ 1,
pK^T_{all,θ}(y|E(x)) ≤ pSC^t_θ(x,y) + c. Moreover, draw the points Xi = (Bi, X̃i) independently and
uniformly from {0,1}^n, where Bi is the first bit and X̃i is the remaining suffix. Set Yi = Bi+1,
with Bm+1 = B1 … Then, for every 0 < θ ≤ 1, the global quantile satisfies
pK^T_{all,θ}(Y|E(X)) ≤ c_cyc for every point vector, whereas, for every integer s ≥ 0,
Pr_X[pSC^t_θ(X,Y) ≤ s] ≤ 2^{2s+2−m}/θ. If ε_n = (m choose 2) 2^{−n} < 1, then the same probability
conditioned on the points being distinct is at most 2^{2s+2−m}/(θ(1−ε_n))."

**Formalization Note.**
1. For every pointwise decoder `U` (published `OWFLocalDesc.Decoder`) and every global decoder
   `V` (`GlobalDecoder`). `T` is a polynomial global clock (`QuantumPRC.EffPoly`, `T ≥ 1`);
   `c` and `c_cyc` are natural numbers chosen before `n`, the data and `θ`.
2. The first inequality is in `ℕ∞` (`∞ + c = ∞`) and holds for every dataset, consistent or not.
3. Probabilities over `X` are counts over all point vectors divided by `2^{m(n)·n}`; the
   conditional one is the ratio over injective point vectors. `Y` is `cyclicLabels`. The exponent
   `2s + 2 − m(n)` is an integer (`zpow`), so the bound may exceed `1`.
4. Point lengths are `n ≥ 1` (needed for the first bit and for `enc(n)`). -/
theorem theorem_B_2 (m t : ℕ → ℕ) (hm : QuantumPRC.EffPoly m) (hm1 : ∀ n, 1 ≤ m n)
    (ht : QuantumPRC.EffPoly t) (ht1 : ∀ n, 1 ≤ t n) (U : Decoder) (V : GlobalDecoder) :
    ∃ T : ℕ → ℕ, QuantumPRC.EffPoly T ∧ (∀ n, 1 ≤ T n) ∧ ∃ c c_cyc : ℕ,
      (∀ n : ℕ, 0 < n → ∀ (x : Fin (m n) → Fin n → Bool) (y : Fin (m n) → Bool) (θ : ℝ),
        0 < θ → θ ≤ 1 → pKT V (T n) θ x y ≤ pSC U (t n) θ x y + (c : ℕ∞)) ∧
      (∀ (n : ℕ) (hn : 0 < n) (θ : ℝ), 0 < θ → θ ≤ 1 →
        ∀ X : Fin (m n) → Fin n → Bool, pKT V (T n) θ X (cyclicLabels hn X) ≤ (c_cyc : ℕ∞)) ∧
      (∀ (n : ℕ) (hn : 0 < n) (θ : ℝ), 0 < θ → θ ≤ 1 → ∀ s : ℕ,
        ((Finset.univ.filter fun X : Fin (m n) → Fin n → Bool =>
            pSC U (t n) θ X (cyclicLabels hn X) ≤ (s : ℕ∞)).card : ℝ) / (2 : ℝ) ^ (m n * n) ≤
          (2 : ℝ) ^ ((2 * s + 2 : ℤ) - (m n : ℤ)) / θ) ∧
      (∀ (n : ℕ) (hn : 0 < n) (θ : ℝ), 0 < θ → θ ≤ 1 →
        ((m n).choose 2 : ℝ) / (2 : ℝ) ^ n < 1 → ∀ s : ℕ,
        ((Finset.univ.filter fun X : Fin (m n) → Fin n → Bool =>
            Function.Injective X ∧ pSC U (t n) θ X (cyclicLabels hn X) ≤ (s : ℕ∞)).card : ℝ) /
          ((Finset.univ.filter fun X : Fin (m n) → Fin n → Bool => Function.Injective X).card : ℝ) ≤
          (2 : ℝ) ^ ((2 * s + 2 : ℤ) - (m n : ℤ)) /
            (θ * (1 - ((m n).choose 2 : ℝ) / (2 : ℝ) ^ n))) := by sorry

end OWFLocalDesc.Supplement
