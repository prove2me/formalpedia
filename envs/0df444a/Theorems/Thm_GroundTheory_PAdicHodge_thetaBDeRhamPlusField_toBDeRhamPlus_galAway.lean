-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_thetaBDeRhamPlusField_toBDeRhamPlus_galAway
-- name    : GroundTheory.PAdicHodge.thetaBDeRhamPlusField_toBDeRhamPlus_galAway
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:06.999546+00:00
-- url     : https://prove2.me/theorems/bd1575fb-e5ff-4c28-bcf9-353ba562ddb3
-- title:
--   PAdic Hodge: theta BDe Rham Plus Field to BDe Rham Plus gal Away
-- statement:
--   The PAdic Hodge construction uses the theta BDe Rham Plus Field to BDe Rham Plus gal Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L267-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L267-L281

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

theorem GroundTheory.PAdicHodge.thetaBDeRhamPlusField_toBDeRhamPlus_galAway (σ : Gal(PadicAlgCl p/K)) (a : 𝔸) :
    IsPerfectoidField.thetaBDeRhamPlusField p (toBDeRhamPlus 𝒪 p (galAway σ a)) =
      σ • IsPerfectoidField.thetaBDeRhamPlusField p (toBDeRhamPlus 𝒪 p a) := by sorry
