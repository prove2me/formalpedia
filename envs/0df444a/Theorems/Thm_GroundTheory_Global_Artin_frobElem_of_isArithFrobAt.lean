-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_frobElem_of_isArithFrobAt
-- name    : GroundTheory.Global.Artin.frobElem_of_isArithFrobAt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:13.343735+00:00
-- url     : https://prove2.me/theorems/c4c1adbe-4973-43b4-a0ff-fb777d847a02
-- title:
--   Artin: frob Elem of is Arith Frob At
-- statement:
--   The Artin construction uses the frob Elem of is Arith Frob At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L121-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L121-L149

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))

theorem GroundTheory.Global.Artin.frobElem_of_isArithFrobAt {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (x : Gal(L/K)) (φx : H) (h : IsArithFrobAt (𝓞 (fixedField H)) φx (x • w.asIdeal)) :
    ∃ i ∈ (MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)),
      (φx : Gal(L/K)) = x * φ ^ (frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal)
        (w.asIdeal.inertia Gal(L/K)) x : ℤ) * x⁻¹ * i := by sorry
