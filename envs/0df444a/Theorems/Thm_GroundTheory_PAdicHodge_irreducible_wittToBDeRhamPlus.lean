-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_irreducible_wittToBDeRhamPlus
-- name    : GroundTheory.PAdicHodge.irreducible_wittToBDeRhamPlus
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:42.756939+00:00
-- url     : https://prove2.me/theorems/63e55651-fa2a-4145-ba80-f95aa270e69d
-- title:
--   PAdic Hodge: irreducible witt To BDe Rham Plus
-- statement:
--   The PAdic Hodge construction uses the irreducible witt To BDe Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L347-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L347-L355

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

theorem GroundTheory.PAdicHodge.irreducible_wittToBDeRhamPlus {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭)
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    Irreducible (wittToBDeRhamPlus R p ξ) := by sorry
