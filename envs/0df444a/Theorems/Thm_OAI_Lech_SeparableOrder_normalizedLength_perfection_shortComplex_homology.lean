-- Prove2me | Theorems.Thm_OAI_Lech_SeparableOrder_normalizedLength_perfection_shortComplex_homology
-- name    : OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:50:51.385461+00:00
-- url     : https://prove2.me/theorems/d7283c9c-2b8d-4a2d-813b-0daad180138d
-- title:
--   OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.SeparableOrder`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`, `open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul`):
--
--   ```lean
--   lemma normalizedLength_perfection_shortComplex_homology
--       (hdim : dimension D = h) (F : CochainComplex (ModuleCat.{u} D) ℤ)
--       (hF : IsFiniteHomologyComplex D F) (i : ℤ) (hi : i < 0) :
--       normalizedLength (Fin h) k p
--         ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
--           (PerfectClosure D p))).obj
--           ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj F).homology i)) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.extendScalars_additive`, `OAI.Lech.PerfectDomainStages.domainAlgebra` and `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L023

section

attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

include K L in
lemma normalizedLength_perfection_shortComplex_homology
    (hdim : dimension D = h) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsFiniteHomologyComplex D F) (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
        (PerfectClosure D p))).obj
        ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj F).homology i)) = 0 := by
  sorry
end Lech.SeparableOrder

end

end OAI
end
