-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_phi_proj
-- name    : GlobalTheory.EisBL.NilAlg.phi_proj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:27.190975+00:00
-- url     : https://prove2.me/theorems/588d78a0-72b4-53d2-a32a-6febd33c62c0
-- title:
--   Nil Alg: phi proj
-- statement:
--   The Nil Alg construction uses the phi proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L104-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.EisBL.NilAlg.phi_proj (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (hh : c h = h)
    (X : Matrix n n B) : phi c J (proj c J K h X) = 0 := by sorry
