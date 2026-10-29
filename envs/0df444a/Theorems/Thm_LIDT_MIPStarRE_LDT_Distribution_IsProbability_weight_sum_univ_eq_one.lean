-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_weight_sum_univ_eq_one
-- name    : LIDT.MIPStarRE.LDT.Distribution.IsProbability.weight_sum_univ_eq_one
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:21.559155+00:00
-- url     : https://prove2.me/theorems/9c082514-59cc-4e0d-a7a4-76373422a78e
-- title:
--   Weight Sum Univ Eq One
-- statement:
--   **A probability distribution has unit mass over the whole finite ambient type.** Let $\alpha$ be finite, let $\mathcal D$ be a distribution on $\alpha$, and suppose $\mathcal D$ has total mass one. Write $w(a)$ for the stored weight of $a$. Because the weights vanish outside the explicit support,
--
--   $$
--   \sum_{a\in\alpha}w(a)=1.
--   $$
--
--   The result supplies the ambient-type normalization used by later finite averages.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Distribution.IsProbability.weight_sum_univ_eq_one`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/Distribution.lean#L130-L140

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






open LIDT.MIPStarRE.LDT.Distribution.IsProbability

theorem LIDT.MIPStarRE.LDT.Distribution.IsProbability.weight_sum_univ_eq_one {α : Type*} [Fintype α]
    {𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α} (h𝒟 : 𝒟.IsProbability) :
    (∑ a : α, 𝒟.weight a) = 1 := by sorry
