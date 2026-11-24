-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_root_norm_sub_untilt_pow_le
-- name    : GroundTheory.PAdicHodge.exists_root_norm_sub_untilt_pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:06.144434+00:00
-- url     : https://prove2.me/theorems/e5e343ef-ade3-45f8-aec6-4a314bcf2feb
-- title:
--   PAdic Hodge: exists root norm sub untilt pow le
-- statement:
--   The PAdic Hodge construction uses the exists root norm sub untilt pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L190-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L190-L220

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

theorem GroundTheory.PAdicHodge.exists_root_norm_sub_untilt_pow_le [IsAlgClosed C♭] {Q : (normInteger C)[X]}
    (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (a : ℕ → 𝒪C♭)
    (ha : ∀ m < Q.natDegree, Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Q.coeff m) =
      PreTilt.coeff 0 (a m))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ∃ b : 𝒪C♭, (monicOfCoeffs Q.natDegree a).eval b = 0 ∧
      ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ Q.natDegree ≤ ‖(p : C)‖ := by sorry
