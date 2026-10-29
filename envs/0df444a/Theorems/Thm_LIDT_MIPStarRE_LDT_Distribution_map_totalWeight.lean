-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_map_totalWeight
-- name    : LIDT.MIPStarRE.LDT.Distribution.map_totalWeight
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:22.354401+00:00
-- url     : https://prove2.me/theorems/eb57c9b9-abb9-463b-991c-503ad0ec5d08
-- title:
--   Map Total Weight
-- statement:
--   **Push-forwards preserve total mass.** Let $\mathcal D$ be a finite-support distribution on $\alpha$ and let $e:\alpha\to\beta$ be a map. Write $\mathcal D_e$ for the push-forward of $\mathcal D$ along $e$, and write $M(\mathcal D)$ for its stored total mass. Then
--
--   $$
--   M(\mathcal D_e)=M(\mathcal D).
--   $$
--
--   This is the mass-conservation fact used to transport the probability invariant through push-forward.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Distribution.map_totalWeight`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/Distribution.lean#L69-L76

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



open LIDT.MIPStarRE.LDT.Distribution

theorem LIDT.MIPStarRE.LDT.Distribution.map_totalWeight {α β : Type*} [DecidableEq β]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (e : α → β) :
    (𝒟.map e).totalWeight = 𝒟.totalWeight := by sorry
