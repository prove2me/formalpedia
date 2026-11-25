-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_phi_gal_smul
-- name    : GroundTheory.PAdicHodge.ACris.phi_gal_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:57.010109+00:00
-- url     : https://prove2.me/theorems/e535b948-1b8d-4913-be4a-80f954d3e3f5
-- title:
--   ACris: phi gal smul
-- statement:
--   The ACris construction uses the phi gal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L282-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L282-L288

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

theorem GroundTheory.PAdicHodge.ACris.phi_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    phi ℂ_[p] p (σ • x) = σ • phi ℂ_[p] p x := by sorry
