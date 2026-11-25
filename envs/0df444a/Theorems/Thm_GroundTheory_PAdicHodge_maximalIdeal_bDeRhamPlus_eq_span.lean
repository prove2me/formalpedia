-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_maximalIdeal_bDeRhamPlus_eq_span
-- name    : GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus_eq_span
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:42.881619+00:00
-- url     : https://prove2.me/theorems/22416e0b-4829-4a75-848e-9805690c3b7c
-- title:
--   PAdic Hodge: maximal Ideal b De Rham Plus eq span
-- statement:
--   The PAdic Hodge construction uses the maximal Ideal b De Rham Plus eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L364-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L364-L369

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

theorem GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus_eq_span {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    maximalIdeal (BDeRhamPlus R p) = span {wittToBDeRhamPlus R p ξ} := by sorry
