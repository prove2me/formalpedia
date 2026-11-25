-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_residueFieldBDeRhamPlusEquiv_residue
-- name    : GroundTheory.PAdicHodge.residueFieldBDeRhamPlusEquiv_residue
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:37.16305+00:00
-- url     : https://prove2.me/theorems/a94f47e9-89dd-4fd1-9452-46dc22afdf09
-- title:
--   PAdic Hodge: residue Field BDe Rham Plus Equiv residue
-- statement:
--   The PAdic Hodge construction uses the residue Field BDe Rham Plus Equiv residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L379-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L379-L385

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
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
open Ideal WittVector IsLocalRing
variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
local notation "𝕎R♭" => WittVector p (PreTilt R p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt R p))

theorem GroundTheory.PAdicHodge.residueFieldBDeRhamPlusEquiv_residue {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R)))
    (x : BDeRhamPlus R p) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    residueFieldBDeRhamPlusEquiv hξ hF hK (residue (BDeRhamPlus R p) x) = thetaBDeRhamPlus R p x := by sorry
