-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_galBdRHom_toBDeRhamPlus
-- name    : GroundTheory.PAdicHodge.galBdRHom_toBDeRhamPlus
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:32.453233+00:00
-- url     : https://prove2.me/theorems/5e095caf-a927-5ed8-ae93-34934f761d23
-- title:
--   PAdic Hodge: gal Bd RHom to BDe Rham Plus
-- statement:
--   The PAdic Hodge construction uses the gal Bd RHom to BDe Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L210-L214

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

theorem GroundTheory.PAdicHodge.galBdRHom_toBDeRhamPlus (σ : Gal(PadicAlgCl p/K)) (a : 𝔸) :
    galBdRHom σ (toBDeRhamPlus 𝒪 p a) = toBDeRhamPlus 𝒪 p (galAway σ a) := by sorry
