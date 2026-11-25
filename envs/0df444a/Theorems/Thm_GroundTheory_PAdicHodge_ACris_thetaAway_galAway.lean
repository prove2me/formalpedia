-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_thetaAway_galAway
-- name    : GroundTheory.PAdicHodge.ACris.thetaAway_galAway
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:59.037777+00:00
-- url     : https://prove2.me/theorems/bf7b5f9d-1bd4-417d-b6d1-7c054a640fe8
-- title:
--   ACris: theta Away gal Away
-- statement:
--   The ACris construction uses the theta Away gal Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L239-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L239-L247

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

theorem GroundTheory.PAdicHodge.ACris.thetaAway_galAway (σ : Gal(PadicAlgCl p/K)) (y : 𝔸) :
    thetaAway ℂ_[p] p (galAway σ y) = σ • thetaAway ℂ_[p] p y := by sorry
