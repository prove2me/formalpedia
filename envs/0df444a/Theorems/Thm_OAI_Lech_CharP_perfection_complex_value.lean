-- Prove2me | Theorems.Thm_OAI_Lech_CharP_perfection_complex_value
-- name    : OAI.Lech.CharP.perfection_complex_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:07:46.325672+00:00
-- url     : https://prove2.me/theorems/5fa6b857-8231-4bad-b33f-16c9c331b16e
-- title:
--   OAI.Lech.CharP.perfection_complex_value: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.CharP`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter`, `open scoped Topology ENNReal`):
--
--   ```lean
--   lemma perfection_complex_value (ell : AllModuleLength (PerfectClosure D p))
--       (hlim : ∀ (M : ModuleCat.{u} D),IsFiniteLength D M →
--         Tendsto (fun n : ℕ => ((p:ℝ≥0∞)^(n*dimension D))⁻¹*
--           (Module.length D (FrobeniusModule D p n M)).toENNReal) atTop
--           (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M))))
--       (hparam : ∀ (z : Fin (dimension D) → D),
--         (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D →
--         ∀ a : ℕ,0<a → ell.value (ModuleCat.of (PerfectClosure D p)
--           ((PerfectClosure D p) ⧸ (parameterIdeal D z a).map (PerfectClosure.of D p))) =
--           (a:ℝ≥0∞)^dimension D*ENNReal.ofReal (Primary.multiplicity (Ideal.span (Set.range z))))
--       (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) (n : ℕ) :
--       (ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj
--         (frobeniusComplex D p n F)).homology 0)).toReal =
--           ((p:ℝ)^n)^dimension D*duttaMultiplicity D p F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.AllModuleLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.CharP.parameterIdeal` (definitions bundle `OAIQ032L002` of this split); `OAI.Lech.FrobeniusModule` and `OAI.Lech.extendScalars_additive` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.Primary.multiplicity` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.dimension`, `OAI.Lech.duttaMultiplicity` and `OAI.Lech.frobeniusComplex` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.CharP.dutta_minimal_estimate` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (IsLocalRing.ResidueField D) p]

lemma perfection_complex_value (ell : AllModuleLength (PerfectClosure D p))
    (hlim : ∀ (M : ModuleCat.{u} D),IsFiniteLength D M →
      Tendsto (fun n : ℕ => ((p:ℝ≥0∞)^(n*dimension D))⁻¹*
        (Module.length D (FrobeniusModule D p n M)).toENNReal) atTop
        (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M))))
    (hparam : ∀ (z : Fin (dimension D) → D),
      (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D →
      ∀ a : ℕ,0<a → ell.value (ModuleCat.of (PerfectClosure D p)
        ((PerfectClosure D p) ⧸ (parameterIdeal D z a).map (PerfectClosure.of D p))) =
        (a:ℝ≥0∞)^dimension D*ENNReal.ofReal (Primary.multiplicity (Ideal.span (Set.range z))))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) (n : ℕ) :
    (ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj
      (frobeniusComplex D p n F)).homology 0)).toReal =
        ((p:ℝ)^n)^dimension D*duttaMultiplicity D p F := by
  sorry
end Lech.CharP

end

end OAI
end
