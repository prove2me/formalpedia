-- Prove2me | Theorems.Thm_OAI_Lech_CharP_dutta_limit_from_perfection
-- name    : OAI.Lech.CharP.dutta_limit_from_perfection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:06:38.960912+00:00
-- url     : https://prove2.me/theorems/ae07d6c6-d06d-4575-a41a-52037fca85d0
-- title:
--   OAI.Lech.CharP.dutta_limit_from_perfection: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.CharP`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter`, `open scoped Topology ENNReal`):
--
--   ```lean
--   lemma dutta_limit_from_perfection (F : CochainComplex (ModuleCat.{u} D) ℤ)
--       (hF : IsFiniteHomologyComplex D F) (ell : AllModuleLength (PerfectClosure D p))
--       (hfinite : ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj
--         (F.homology 0)) ≠ ⊤)
--       (hlim : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*dimension D))⁻¹ *
--         (Module.length D (FrobeniusModule D p n (F.homology 0))).toENNReal) atTop
--         (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj (F.homology 0))))) :
--       Tendsto (duttaSequence D p F) atTop
--         (𝓝 ((ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex
--           (.up ℤ)).obj F).homology 0)).toReal))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.AllModuleLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.FrobeniusModule` and `OAI.Lech.extendScalars_additive` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.dimension` and `OAI.Lech.duttaSequence` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proofs of `OAI.Lech.CharP.perfection_complex_value` and `OAI.Lech.cyclicDuttaSequence_tendsto` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L005

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

lemma dutta_limit_from_perfection (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsFiniteHomologyComplex D F) (ell : AllModuleLength (PerfectClosure D p))
    (hfinite : ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj
      (F.homology 0)) ≠ ⊤)
    (hlim : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*dimension D))⁻¹ *
      (Module.length D (FrobeniusModule D p n (F.homology 0))).toENNReal) atTop
      (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj (F.homology 0))))) :
    Tendsto (duttaSequence D p F) atTop
      (𝓝 ((ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex
        (.up ℤ)).obj F).homology 0)).toReal)) := by
  sorry

end Lech.CharP

end

end OAI
end
