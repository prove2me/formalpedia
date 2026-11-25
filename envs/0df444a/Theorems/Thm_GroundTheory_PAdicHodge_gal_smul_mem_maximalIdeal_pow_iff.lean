-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_mem_maximalIdeal_pow_iff
-- name    : GroundTheory.PAdicHodge.gal_smul_mem_maximalIdeal_pow_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:42.26688+00:00
-- url     : https://prove2.me/theorems/d6c9d387-7151-554e-a63b-fecd2ee362a5
-- title:
--   PAdic Hodge: gal smul mem maximal Ideal pow iff
-- statement:
--   The PAdic Hodge construction uses the gal smul mem maximal Ideal pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L308-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L308-L316

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

theorem GroundTheory.PAdicHodge.gal_smul_mem_maximalIdeal_pow_iff (σ : Gal(PadicAlgCl p/K)) (x : 𝔹) (n : ℕ) :
    σ • x ∈ maximalIdeal 𝔹 ^ n ↔ x ∈ maximalIdeal 𝔹 ^ n := by sorry
