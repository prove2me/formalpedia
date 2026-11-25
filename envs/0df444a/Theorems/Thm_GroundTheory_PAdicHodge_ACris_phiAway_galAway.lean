-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_phiAway_galAway
-- name    : GroundTheory.PAdicHodge.ACris.phiAway_galAway
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:14.156708+00:00
-- url     : https://prove2.me/theorems/06986eb7-c03d-51bd-b201-93a97751224d
-- title:
--   ACris: phi Away gal Away
-- statement:
--   The ACris construction uses the phi Away gal Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L269-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L269-L275

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

theorem GroundTheory.PAdicHodge.ACris.phiAway_galAway (σ : Gal(PadicAlgCl p/K)) (y : 𝔸) :
    phiAway ℂ_[p] p (galAway σ y) = galAway σ (phiAway ℂ_[p] p y) := by sorry
