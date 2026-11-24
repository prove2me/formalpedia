-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_prod_sub_untilt_le
-- name    : GroundTheory.PAdicHodge.norm_prod_sub_untilt_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:06.442443+00:00
-- url     : https://prove2.me/theorems/65d73b26-6b2c-446d-aba9-269da4d18f4f
-- title:
--   PAdic Hodge: norm prod sub untilt le
-- statement:
--   The PAdic Hodge construction uses the norm prod sub untilt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L135-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L135-L155

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
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
open Polynomial
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.norm_prod_sub_untilt_le (s : Multiset 𝒪C♭) {Q : (normInteger C)[X]}
    (hQ : Q.map (Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})) =
      ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ‖(s.map fun b => (z : C) - ((PreTilt.untilt b : normInteger C) : C)).prod‖ ≤ ‖(p : C)‖ := by sorry
