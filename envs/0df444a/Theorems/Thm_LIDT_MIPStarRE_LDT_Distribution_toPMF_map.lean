-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_toPMF_map
-- name    : LIDT.MIPStarRE.LDT.Distribution.toPMF_map
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:19.009243+00:00
-- url     : https://prove2.me/theorems/db673bfb-e634-46ea-abc9-d30477a8437f
-- title:
--   To PMF Map
-- statement:
--   **The project and Mathlib push-forwards agree.** Let $\mathcal D$ be a probability distribution on $\alpha$, let $e:\alpha\to\beta$ be a map, and write $\mathcal D_e$ for its push-forward. Denote the associated PMFs by $P_{\mathcal D}$ and $P_{\mathcal D_e}$. Then
--
--   $$
--   P_{\mathcal D_e}=\operatorname{map}(P_{\mathcal D},e).
--   $$
--
--   This is the bridge between the explicit-support distribution representation and Mathlib probability calculations.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Distribution.toPMF_map`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/Distribution.lean#L195-L218

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map

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

theorem LIDT.MIPStarRE.LDT.Distribution.toPMF_map {α β : Type*} [DecidableEq β]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (h𝒟 : 𝒟.IsProbability) (e : α → β) :
    (𝒟.map e).toPMF (h𝒟.map e) = (𝒟.toPMF h𝒟).map e := by sorry
