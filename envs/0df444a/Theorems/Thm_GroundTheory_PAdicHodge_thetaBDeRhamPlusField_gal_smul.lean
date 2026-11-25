-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_thetaBDeRhamPlusField_gal_smul
-- name    : GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:48.917619+00:00
-- url     : https://prove2.me/theorems/27d4c305-353b-4e52-a39c-fc1295fbf3fc
-- title:
--   PAdic Hodge: theta BDe Rham Plus Field gal smul
-- statement:
--   The PAdic Hodge construction uses the theta BDe Rham Plus Field gal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L283-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L283-L301

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

theorem GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : 𝔹) :
    IsPerfectoidField.thetaBDeRhamPlusField p (σ • x) =
      σ • IsPerfectoidField.thetaBDeRhamPlusField p x := by sorry
