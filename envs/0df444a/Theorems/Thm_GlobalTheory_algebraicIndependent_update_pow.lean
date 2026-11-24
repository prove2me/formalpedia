-- Prove2me | Theorems.Thm_GlobalTheory_algebraicIndependent_update_pow
-- name    : GlobalTheory.algebraicIndependent_update_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:50.564401+00:00
-- url     : https://prove2.me/theorems/4b9a290e-9c24-41f2-b11d-ea45ca279320
-- title:
--   Global Theory: algebraic Independent update pow
-- statement:
--   The Global Theory construction uses the algebraic Independent update pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAlgHomInjectiveApplyOfTranscendental.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAlgHomInjectiveApplyOfTranscendental.lean#L8-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAlgHomInjectiveApplyOfTranscendental
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.algebraicIndependent_update_pow {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] {x : ι → A} (hx : AlgebraicIndependent R x) (i₀ : ι) {n : ℕ} (hn : 0 < n) :
    AlgebraicIndependent R (Function.update x i₀ (x i₀ ^ n)) := by sorry
