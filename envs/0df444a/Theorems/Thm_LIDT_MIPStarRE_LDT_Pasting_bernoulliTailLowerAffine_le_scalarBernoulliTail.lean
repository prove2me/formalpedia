-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_bernoulliTailLowerAffine_le_scalarBernoulliTail
-- name    : LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine_le_scalarBernoulliTail
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T15:57:46.584992+00:00
-- url     : https://prove2.me/theorems/2b2e3be1-68da-4f93-b738-e6d904aceadf
-- title:
--   Bernoulli Tail Lower Affine Le Scalar Bernoulli Tail
-- statement:
--   **Affine lower envelope for the scalar Bernoulli tail.** Let $0<\theta<1$, let `k` and `degree` be natural numbers, and write $d_0$ for `degree`. Assume
--
--   $$
--   \frac{2d_0}{\theta}\le k.
--   $$
--
--   For $p\in[0,1]$, write $\mathcal A(\theta,c,p)$ for the affine lower envelope and $\mathcal B(k,d_0,p)$ for the scalar binomial tail. With $c=\exp(-\theta^2k/2)$, the theorem states
--
--   $$
--   \mathcal A\!\left(\theta,\exp\!\left(-\frac{\theta^2 k}{2}\right),p\right)
--   \le \mathcal B(k,d_0,p).
--   $$
--
--   The scalar tail is
--
--   $$
--   \mathcal B(k,d_0,p)=\sum_{r=d_0+1}^{k}\binom{k}{r}p^r(1-p)^{k-r},
--   $$
--
--   while the affine expression is $(1-c)-(1-p)/(1-\theta)$. The proof combines the Hoeffding lower estimate in the region $p\ge\theta$ with nonnegativity of the tail when $p<\theta$. This theorem is the scalar input to `chernoffBernoulliMatrix`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine_le_scalarBernoulliTail`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean#L440-L511

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

open LIDT
/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff comparison.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine_le_scalarBernoulliTail
    (theta : _root_.LIDT.MIPStarRE.LDT.Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : _root_.LIDT.MIPStarRE.LDT.Error)) / theta ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error))
    {p : _root_.LIDT.MIPStarRE.LDT.Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta
      (Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2)) p ≤
        _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree p := by sorry
