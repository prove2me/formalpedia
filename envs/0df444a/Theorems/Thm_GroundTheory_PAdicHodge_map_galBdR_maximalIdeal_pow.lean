-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_galBdR_maximalIdeal_pow
-- name    : GroundTheory.PAdicHodge.map_galBdR_maximalIdeal_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:28.896459+00:00
-- url     : https://prove2.me/theorems/e889498c-3b22-59ba-9633-ffebb6bf300b
-- title:
--   PAdic Hodge: map gal Bd R maximal Ideal pow
-- statement:
--   The PAdic Hodge construction uses the map gal Bd R maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L318-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L318-L327

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
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
open Ideal WittVector IsLocalRing
open GroundTheory GroundTheory.PAdicHodge
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝒪" => normInteger ℂ_[p]
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger ℂ_[p]) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger ℂ_[p]) p))
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger ℂ_[p]) p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p

theorem GroundTheory.PAdicHodge.map_galBdR_maximalIdeal_pow (σ : Gal(PadicAlgCl p/K)) (n : ℕ) :
    (maximalIdeal 𝔹 ^ n).map (galBdR σ) = maximalIdeal 𝔹 ^ n := by sorry
