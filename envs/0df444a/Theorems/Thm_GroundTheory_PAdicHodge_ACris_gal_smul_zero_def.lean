-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_gal_smul_zero_def
-- name    : GroundTheory.PAdicHodge.ACris.gal_smul_zero_def
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:34.753886+00:00
-- url     : https://prove2.me/theorems/894c3f2b-2503-5780-9b03-789527a9e257
-- title:
--   ACris: gal smul zero def
-- statement:
--   The ACris construction uses the gal smul zero def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L173-L175

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

theorem GroundTheory.PAdicHodge.ACris.gal_smul_zero_def (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    σ • y = galZero σ y := by sorry
