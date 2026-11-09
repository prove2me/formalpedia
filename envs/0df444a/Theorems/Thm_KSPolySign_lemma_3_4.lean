-- Prove2me | Theorems.Thm_KSPolySign_lemma_3_4
-- name    : KSPolySign.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:05.259286+00:00
-- url     : https://prove2.me/theorems/b4b19790-adda-4ad5-97e6-c23ffbaede87
-- title:
--   Lemma 3.4 — coordinate weight and potential bounds
-- statement:
--   Let $\beta(t)=\sqrt{1-t^2}$, $\iota=3.03$, and let $P$ be the matrix potential with parameter $\rho>0$.
--
--   1. $\beta$ is nonnegative and continuous on $[-1,1]$, smooth on $(-1,1)$, and $\beta(\pm1)=0$, $\beta(0)=1$, $1-t^2\le\beta(t)\le1$ for $t\in[-1,1]$.
--   2. For every $y\in[-1,1]^k$ every feasible point $(b,U,V)$ satisfies $b>\|M(y)\|$, and $\|M(y)\|\le P(y)$. If moreover $M(y)=\sum_iy_iC_i$ (no fixed part) and $\bar\zeta\ge\|\sum_iC_i^2\|$, then
--   $$P(0)\le 2\sqrt{\iota\bar\zeta+2n\rho}.$$
--
--   The potential therefore controls the norm of the signed sum, and starts below $2\sqrt{\iota\bar\zeta}$ up to the regularization.
--
--   Differences from the source:
--   - generalization: the normalized inputs Ā_i of Lemma 3.1 and ζ̄ ≥ ζ = ‖∑Ā_i²‖ → (b) for every maintained instance C (PSD rank-one, ∑C_i² ⪯ I) and ρ > 0: the first two claims for any Hermitian F, the bound on P(0) for F = 0 and any ζ̄ ≥ ‖∑C_i²‖; reason: Definition 3.5 evaluates the notation with C_i; the proof uses only M(0) = 0 and K_0(I) ⪯ ιζ̄I; the normalized inputs are such an instance
--   - encoding: smooth on (−1, 1) → ContDiffOn ℝ ∞ on the open interval; reason: Lean convention; same meaning
--   - encoding: matrices in ℂ^{n×n} with nonzero inputs (so n ≥ 1) → explicit hypothesis 1 ≤ n; reason: excludes only 0×0 matrices, where the program of Definition 3.3 is degenerate and P has no meaning
--   - encoding: operator norm ‖·‖ induced by the Euclidean norm; ‖X‖^{1/2} → AgnosticTNS.opNorm (sup of ‖Xv‖ over the Euclidean unit ball); Real.sqrt; reason: Lean convention; same values
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.4, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_KSPolySign_pot
import Definitions.Def_KSPolySign_IsInstance
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 3.4 (Coordinate weight and potential bounds).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.4, p.18 (PDF p.18).

(a) `β` is nonnegative and continuous on `[−1, 1]`, smooth on `(−1, 1)`, `β(±1) = 0`, `β(0) = 1`, and
`1 − t² ≤ β(t) ≤ 1` on `[−1, 1]`. (b) For every `y ∈ [−1, 1]^k` each feasible point satisfies
`b > ‖M(y)‖`, `‖M(y)‖ ≤ P(y)`, and, for `M(y) = ∑ y_iC_i` (no fixed part) and `ζ̄ ≥ ‖∑ C_i²‖`,
`P(0) ≤ 2√(ιζ̄ + 2nρ)`.

**Formalization Note** Part (b) is stated for every maintained instance (Definition 3.5) with
`ρ > 0`; the normalized inputs of Lemma 3.1 are the case `F = 0`, `C_i = Ā_i`. "Smooth" is
`ContDiffOn ℝ ∞`. `‖·‖` is the Euclidean operator norm (`AgnosticTNS.opNorm`, published); `‖X‖^{1/2}` is `Real.sqrt`. `n ≥ 1` excludes `0 × 0` matrices. -/
theorem lemma_3_4 :
    ((∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ beta t) ∧ ContinuousOn beta (Set.Icc (-1) 1) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) beta (Set.Ioo (-1) 1) ∧
      beta (-1) = 0 ∧ beta 1 = 0 ∧ beta 0 = 1 ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 - t ^ 2 ≤ beta t ∧ beta t ≤ 1) ∧
    ∀ (n k : ℕ), 1 ≤ n → ∀ C : Fin k → Matrix (Fin n) (Fin n) ℂ, IsInstance C → ∀ ρ : ℝ, 0 < ρ →
      (∀ F : Matrix (Fin n) (Fin n) ℂ, F.IsHermitian → ∀ y : Fin k → ℝ, (∀ i, |y i| ≤ 1) →
        (∀ (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ), Feasible C F y b U V → AgnosticTNS.opNorm (Msum C F y) < b) ∧
        AgnosticTNS.opNorm (Msum C F y) ≤ pot C F ρ y) ∧
      ∀ ζbar : ℝ, AgnosticTNS.opNorm (∑ i, C i * C i) ≤ ζbar →
        pot C 0 ρ 0 ≤ 2 * Real.sqrt (iota * ζbar + 2 * n * ρ) := by sorry

end KSPolySign
