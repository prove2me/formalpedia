-- Prove2me | Theorems.Thm_GlobalTheory_roots_taylor_eq_map_sub
-- name    : GlobalTheory.roots_taylor_eq_map_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:12.32988+00:00
-- url     : https://prove2.me/theorems/ef05ebee-dfc6-4b62-9b9b-5aea6fda386d
-- title:
--   Global Theory: roots taylor eq map sub
-- statement:
--   The Global Theory construction uses the roots taylor eq map sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FewRootsSmallDisc.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FewRootsSmallDisc.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory

theorem GlobalTheory.roots_taylor_eq_map_sub {K : Type*} [Field K] (p : K[X]) (w : K) :
    (taylor w p).roots = p.roots.map (fun x => x - w) := by sorry
