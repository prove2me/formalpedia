-- Prove2me | Theorems.Thm_KunenZF_suzuki_no_definable_reinhardt_nonempty
-- name    : KunenZF.suzuki_no_definable_reinhardt_nonempty
-- status  : Proved
-- author  : @teargosling
-- created : 2026-11-27T05:11:04.849706+00:00
-- url     : https://prove2.me/theorems/037df04f-d4ee-4c40-8484-dff0349a9832
-- title:
--   Suzuki's theorem: no nontrivial elementary $j : V \to V$ is definable from parameters (nonempty model)
-- statement:
--   For every pure $\{\in\}$-formula $\delta(x, y, \vec{p})$ (possibly with arbitrary set parameters $\vec{p}$), the Reinhardt theory $\mathrm{ZF}(j) + \text{"$j : V \to V$ is a nontrivial elementary embedding"}$ together with the assertion that the graph of $j$ is defined by $\delta$ from some parameters has no nonempty model $M$:
--
--   $$\neg\bigl(M \models \mathrm{reinhardtDefinableTheory}(\delta)\bigr).$$
--
--   This is Suzuki's theorem (1999), the strongest known $\mathrm{ZF}$-only negative result toward the Kunen inconsistency without Choice: it rules out every first-order definable nontrivial elementary embedding $j : V \to V$, even allowing arbitrary set parameters.
--
--   **Formalization Note:** This adds the standard first-order nonemptiness hypothesis `[Nonempty M]` missing from `KunenZF.suzuki_no_definable_reinhardt` (without `[Nonempty M]`, the empty structure `PEmpty.{u + 1}` vacuously satisfies every universally closed sentence `close φ` and `closeJ ψ` in `reinhardtDefinableTheory δ`).
-- source:
--   Akira Suzuki, No elementary embedding from V into V is definable from parameters, J. Symbolic Logic 64 (1999), no. 4, 1591-1594, https://doi.org/10.2307/2586799 (main theorem).

import Mathlib.ModelTheory.Semantics
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

universe u

open FirstOrder FirstOrder.Language

namespace KunenZF
theorem suzuki_no_definable_reinhardt_nonempty {M : Type u} [setLangJ.Structure M] [Nonempty M]
    (δ : ContinuumHypothesis.SFormula) :
    ¬ (M ⊨ reinhardtDefinableTheory δ) := by sorry
end KunenZF
