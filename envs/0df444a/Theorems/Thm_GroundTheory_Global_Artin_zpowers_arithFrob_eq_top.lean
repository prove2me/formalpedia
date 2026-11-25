-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_zpowers_arithFrob_eq_top
-- name    : GroundTheory.Global.Artin.zpowers_arithFrob_eq_top
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:07.744558+00:00
-- url     : https://prove2.me/theorems/c8bd176d-7289-46b1-8fd1-4e9f1a46c7fc
-- title:
--   Artin: zpowers arith Frob eq top
-- statement:
--   The Artin construction uses the zpowers arith Frob eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InductionFrobenius.lean#L15-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InductionFrobenius.lean#L15-L50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Definitions.Def_GroundTheory_GlobalFields_Artin_InductionFrobenius
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
open NumberField IsDedekindDomain
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem GroundTheory.Global.Artin.zpowers_arithFrob_eq_top (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) :
    Subgroup.zpowers ((⟨φ, hφ.mem_stabilizer⟩ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
      MulAction.stabilizer Gal(L/K) w.asIdeal ⧸
        (w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)) =
      ⊤ := by sorry
