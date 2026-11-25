-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_galCris_of
-- name    : GroundTheory.PAdicHodge.ACris.galCris_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:15.929752+00:00
-- url     : https://prove2.me/theorems/96d6d280-c7d2-4432-919e-d36df0614760
-- title:
--   ACris: gal Cris of
-- statement:
--   The ACris construction uses the gal Cris of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L201-L203

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

theorem GroundTheory.PAdicHodge.ACris.galCris_of (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    galCris σ (AdicCompletion.of _ _ y) = AdicCompletion.of _ _ (σ • y) := by sorry
