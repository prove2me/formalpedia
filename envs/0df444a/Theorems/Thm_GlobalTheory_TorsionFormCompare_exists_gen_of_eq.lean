-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFormCompare_exists_gen_of_eq
-- name    : GlobalTheory.TorsionFormCompare.exists_gen_of_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:15.780035+00:00
-- url     : https://prove2.me/theorems/fb4e39d2-7a0b-49c8-9d42-bf33b75ffcf8
-- title:
--   Torsion Form Compare: exists gen of eq
-- statement:
--   The Torsion Form Compare construction uses the exists gen of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIdentityPullbackDegeneration.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIdentityPullbackDegeneration.lean#L15-L22

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

theorem GlobalTheory.TorsionFormCompare.exists_gen_of_eq {X Y : Scheme.{0}} (L : LB X) {p q : Y ⟶ X} (h : q = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => q) (fun _ => n)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → L.ι),
        gm r z (LB.wchart L (fun _ => q) j) (b.s j) = gm r z (LB.wchart L (fun _ => p) j) (a.s j)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by sorry
