-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_gal_smul_of
-- name    : GroundTheory.PAdicHodge.ACris.gal_smul_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:16.808291+00:00
-- url     : https://prove2.me/theorems/951cbb8d-1e07-47b0-beb6-431abc146f38
-- title:
--   ACris: gal smul of
-- statement:
--   The ACris construction uses the gal smul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L228-L231

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

theorem GroundTheory.PAdicHodge.ACris.gal_smul_of (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    σ • AdicCompletion.of (Ideal.span {(p : ACrisZero ℂ_[p] p)}) _ y =
      AdicCompletion.of _ _ (σ • y) := by sorry
