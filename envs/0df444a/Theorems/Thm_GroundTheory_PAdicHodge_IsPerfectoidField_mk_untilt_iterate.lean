-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt_iterate
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.mk_untilt_iterate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:51.664448+00:00
-- url     : https://prove2.me/theorems/d76bcc57-0d8f-4b16-99dd-4637c086d1b7
-- title:
--   Is Perfectoid Field: mk untilt iterate
-- statement:
--   The Is Perfectoid Field construction uses the mk untilt iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L155-L158

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p

theorem GroundTheory.PAdicHodge.IsPerfectoidField.mk_untilt_iterate (x : 𝒪♭) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝒪)})
      (PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x)) = PreTilt.coeff n x := by sorry
