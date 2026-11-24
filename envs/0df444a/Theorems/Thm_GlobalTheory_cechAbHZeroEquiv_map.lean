-- Prove2me | Theorems.Thm_GlobalTheory_cechAbHZeroEquiv_map
-- name    : GlobalTheory.cechAbHZeroEquiv_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:50:24.35754+00:00
-- url     : https://prove2.me/theorems/1a31ebaa-ef16-4034-847c-92b93d40f28a
-- title:
--   Global Theory: cech Ab HZero Equiv map
-- statement:
--   The Global Theory construction uses the cech Ab HZero Equiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L595-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L595-L602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : TopCat.{w}} {ι : Type} {P Q : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{w}}
  {V : Opens T} {U : ι → Opens T}
variable [LinearOrder ι]

theorem GlobalTheory.cechAbHZeroEquiv_map (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hQ : Presheaf.IsSheaf (Opens.grothendieckTopology T) Q) (hc : V ≤ ⨆ i, U i) (φ : P ⟶ Q)
    (x : cechAbH P V U 0) :
    cechAbHZeroEquiv hQ hc ((cechAbHMap V U φ 0).hom x) =
      φ.app (op V) (cechAbHZeroEquiv hP hc x) := by sorry
