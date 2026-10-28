-- Prove2me | Theorems.Thm_OAI_Lech_CharP_normalized_perfection_module_finite
-- name    : OAI.Lech.CharP.normalized_perfection_module_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:08:06.76996+00:00
-- url     : https://prove2.me/theorems/e5d95b67-7948-4767-a424-83cfcf48643a
-- title:
--   OAI.Lech.CharP.normalized_perfection_module_finite: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.CharP`, with `open CategoryTheory CategoryTheory.Limits`, `open scoped ENNReal`, `open IsLocalRing`):
--
--   ```lean
--   lemma normalized_perfection_module_finite (ell : AllModuleLength (PerfectClosure D p))
--       (hparam : ∀ (z : Fin (dimension D) → D),
--         (Ideal.span (Set.range z)).radical = maximalIdeal D → ∀ a : ℕ,0<a →
--         ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
--           (parameterIdeal D z a).map (PerfectClosure.of D p))) =
--           (a:ℝ≥0∞)^(dimension D) * ENNReal.ofReal (Primary.multiplicity (Ideal.span (Set.range z))))
--       (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
--       ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M) ≠ ⊤
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.AllModuleLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.CharP.parameterIdeal` (definitions bundle `OAIQ032L002` of this split); `OAI.Lech.Primary.multiplicity` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proofs of `OAI.Lech.CharP.perfection_complex_value` and `OAI.Lech.cyclicDuttaSequence_tendsto` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal
namespace Lech.CharP
open IsLocalRing
universe u
variable (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
lemma normalized_perfection_module_finite (ell : AllModuleLength (PerfectClosure D p))
    (hparam : ∀ (z : Fin (dimension D) → D),
      (Ideal.span (Set.range z)).radical = maximalIdeal D → ∀ a : ℕ,0<a →
      ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
        (parameterIdeal D z a).map (PerfectClosure.of D p))) =
        (a:ℝ≥0∞)^(dimension D) * ENNReal.ofReal (Primary.multiplicity (Ideal.span (Set.range z))))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
    ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M) ≠ ⊤ := by
  sorry
end Lech.CharP

end

end OAI
end
