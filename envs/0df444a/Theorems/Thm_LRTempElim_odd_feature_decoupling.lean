-- Prove2me | Theorems.Thm_LRTempElim_odd_feature_decoupling
-- name    : LRTempElim.odd_feature_decoupling
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:06.895233+00:00
-- url     : https://prove2.me/theorems/db068827-02de-4021-9b3d-eddd060debc9
-- title:
--   §A.2.3: the odd feature decouples; $C_{\mathrm{NCE}}(a)\ge(1+a^2/4)/(2I_a)$
-- statement:
--   For the Gaussian family with features $\phi=(1,x,x^2)$, let $V=V_{\mathrm{NCE}}(a)=H_a^{-1}S_aH_a^{-1}$ be the balanced logistic sandwich covariance and $\Sigma=\Sigma_{\nu_a}$ the feature second-moment matrix, and let $I_a=\mathbb E_{\nu_a}[X^2\sigma(aX)(1-\sigma(aX))]$. For every real $a$:
--
--   1. symmetry decouples the odd feature $x$ (index $1$) from $1$ and $x^2$: $V_{01}=V_{10}=V_{21}=V_{12}=0$ and $\Sigma_{01}=\Sigma_{10}=\Sigma_{21}=\Sigma_{12}=0$;
--   2. the covariance entry of the odd feature is $V_{11}=1/(2I_a)$, and $\Sigma_{11}=1+a^2/4$;
--   3. the query risk splits as
--   $$
--   C_{\mathrm{NCE}}(a)=\frac{1+a^2/4}{2I_a}+\sum_{i,j\in\{0,2\}}\Sigma_{ij}V_{ji},
--   $$
--   and the remaining even-feature risk $\sum_{i,j\in\{0,2\}}\Sigma_{ij}V_{ji}$ is nonnegative.
--
--   Hence $C_{\mathrm{NCE}}(a)\ge(1+a^2/4)/(2I_a)$, which reduces the exponential lower bound in the goal theorem to the asymptotics of $I_a$.
--
--   Differences from the source:
--   - reading: "symmetry decouples the odd feature x from 1, x²" → the entries of V_NCE(a) and Σ_{ν_a} between index 1 and indices 0, 2 vanish; reason: the meaning of block decoupling for both matrices of the trace
--   - reading: "its contribution to the query risk" and "the remaining even-feature risk" → the split tr(ΣV) = Σ₁₁V₁₁ + Σ_{i,j∈{0,2}} Σ_ij V_ji; reason: the trace of a block-diagonal product splits blockwise
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §A.2.3, p.20 (pdf p.22)

import Mathlib
import Definitions.Def_LRTempElim_Logistic

open MeasureTheory ProbabilityTheory Matrix

namespace LRTempElim

/-- **Decoupling of the odd feature** (§A.2.3). Chen, Wu, Yang, Zeng, *Likelihood-Ratio Learning
under Weak Overlap via Analytic Temporal Elimination*, STOC 2027 submission (manuscript of
2026-11-03, sha256 eee65139…), §A.2.3, p.20 (pdf p.22).

"Define `I_a = E_{ν_a}[X²σ(aX)(1 − σ(aX))]`. … Symmetry decouples the odd feature x from 1, x².
Its covariance entry is `1/(2I_a)` and its contribution to the query risk is `(1 + a²/4)/(2I_a)`.
The remaining even-feature risk is nonnegative."

**Formalization Note.** Features `ϕ = (1, x, x²)`, 0-based (index 1 is the odd feature `x`).
"Decouples" is: the off-diagonal entries between index 1 and indices 0, 2 vanish in both
`V_NCE(a)` and `Σ_{ν_a}`. The query risk is `C_NCE(a) = tr(Σ_{ν_a}V_NCE(a))`; it splits into the
odd contribution `Σ₁₁V₁₁ = (1 + a²/4)/(2I_a)` and the even-block sum `Σ_{i,j∈{0,2}} Σ_{ij}V_{ji}`,
which is nonnegative. Stated for every real `a`. -/
theorem odd_feature_decoupling (a : ℝ) :
    let V := Vnce a
    let Sm := secondMoment phi3 (nu a)
    let even : Finset (Fin 3) := {0, 2}
    V 1 1 = 1 / (2 * Ia a) ∧
      V 0 1 = 0 ∧ V 1 0 = 0 ∧ V 2 1 = 0 ∧ V 1 2 = 0 ∧
      Sm 1 1 = 1 + a ^ 2 / 4 ∧
      Sm 0 1 = 0 ∧ Sm 1 0 = 0 ∧ Sm 2 1 = 0 ∧ Sm 1 2 = 0 ∧
      Cnce a = (1 + a ^ 2 / 4) / (2 * Ia a) + ∑ i ∈ even, ∑ j ∈ even, Sm i j * V j i ∧
      0 ≤ ∑ i ∈ even, ∑ j ∈ even, Sm i j * V j i := by sorry

end LRTempElim
