-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_gal_smul_zero
-- name    : GroundTheory.PAdicHodge.ACris.coe_gal_smul_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:35.796732+00:00
-- url     : https://prove2.me/theorems/db04c700-7be3-476b-9cec-3a8976473edc
-- title:
--   ACris: coe gal smul zero
-- statement:
--   The ACris construction uses the coe gal smul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L177-L179

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)

theorem GroundTheory.PAdicHodge.ACris.coe_gal_smul_zero (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    ((σ • y : ACrisZero ℂ_[p] p) : 𝔸) = galAway σ y := by sorry
