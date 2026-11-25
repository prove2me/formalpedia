-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_mk_pow_smul_of_isArithFrobAt
-- name    : GroundTheory.Global.Artin.mk_pow_smul_of_isArithFrobAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:21.716146+00:00
-- url     : https://prove2.me/theorems/8c4d4edf-7aa2-4cbb-9fdf-0c5c9d1a523c
-- title:
--   Artin: mk pow smul of is Arith Frob At
-- statement:
--   The Artin construction uses the mk pow smul of is Arith Frob At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L98-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L98-L107

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

theorem GroundTheory.Global.Artin.mk_pow_smul_of_isArithFrobAt {P : Ideal (𝓞 L)} {ψ : Gal(L/K)}
    (hψ : IsArithFrobAt (𝓞 K) ψ P) (n : ℕ) (y : 𝓞 L) :
    Ideal.Quotient.mk P ((ψ ^ n) • y) =
      Ideal.Quotient.mk P y ^ (Nat.card (𝓞 K ⧸ P.under (𝓞 K)) ^ n) := by sorry
