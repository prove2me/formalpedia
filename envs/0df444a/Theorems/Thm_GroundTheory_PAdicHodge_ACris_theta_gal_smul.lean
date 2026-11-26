-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_gal_smul
-- name    : GroundTheory.PAdicHodge.ACris.theta_gal_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:40.361409+00:00
-- url     : https://prove2.me/theorems/2a9650fa-b547-594b-83e7-7ec05e58c8d6
-- title:
--   ACris: theta gal smul
-- statement:
--   The ACris construction uses the theta gal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L254-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L254-L267

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

theorem GroundTheory.PAdicHodge.ACris.theta_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    ((theta ℂ_[p] p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((theta ℂ_[p] p x : normInteger ℂ_[p]) : ℂ_[p]) := by sorry
