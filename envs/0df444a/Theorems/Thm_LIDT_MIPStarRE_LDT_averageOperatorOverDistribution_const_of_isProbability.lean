-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_averageOperatorOverDistribution_const_of_isProbability
-- name    : LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_const_of_isProbability
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:35.982238+00:00
-- url     : https://prove2.me/theorems/7ebfccca-4e60-4f83-b480-2aac3561fd5f
-- title:
--   Average Operator Over Distribution Const Of Is Probability
-- statement:
--   **A constant operator averages to itself under a probability distribution.**
--
--   Let $\mathcal{D}$ be a finitely supported probability distribution on a question type and let $A$ be an operator on a finite index set. The operator-valued average of the constant family $a\mapsto A$ is $A$ because the distribution weights sum to one.
--
--   $$
--   \operatorname{averageOperatorOverDistribution}\,\mathcal{D}\,(a\mapsto A)=A.
--   $$
--
--   The identity is used in the pasting step when constant operator families are inserted into averaged sandwich expressions.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.averageOperatorOverDistribution_const_of_isProbability`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/Distribution.lean#L370-L377

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open LIDT
/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support weighted distributions,
a probability predicate, push-forward distributions, weighted-sum linear maps,
averaging, uniform distribution, and outcome summation.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

theorem LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_const_of_isProbability {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (h𝒟 : 𝒟.IsProbability) (A : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟 (fun _ : α => A) = A := by sorry
