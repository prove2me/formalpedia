-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFormCompare_exists_mapsAt_id
-- name    : GlobalTheory.TorsionFormCompare.exists_mapsAt_id
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:01.24625+00:00
-- url     : https://prove2.me/theorems/bc0f117e-7fe1-49ab-8afb-eada50955750
-- title:
--   Torsion Form Compare: exists maps At id
-- statement:
--   The Torsion Form Compare construction uses the exists maps At id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIdentityPullbackDegeneration.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIdentityPullbackDegeneration.lean#L24-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIdentityPullbackDegeneration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare

theorem GlobalTheory.TorsionFormCompare.exists_mapsAt_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (ha : a.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L (J := PUnit) (fun _ => F) (isoPullId (idIso L) hF) p n a b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by sorry
