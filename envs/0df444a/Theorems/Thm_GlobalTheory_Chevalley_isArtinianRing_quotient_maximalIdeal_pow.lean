-- Prove2me | Theorems.Thm_GlobalTheory_Chevalley_isArtinianRing_quotient_maximalIdeal_pow
-- name    : GlobalTheory.Chevalley.isArtinianRing_quotient_maximalIdeal_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:37.549631+00:00
-- url     : https://prove2.me/theorems/abcf1d0a-5857-4670-9e17-121884f7e2cc
-- title:
--   Chevalley: is Artinian Ring quotient maximal Ideal pow
-- statement:
--   The Chevalley construction uses the is Artinian Ring quotient maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L9-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Chevalley

theorem GlobalTheory.Chevalley.isArtinianRing_quotient_maximalIdeal_pow (B : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (k : ℕ) : IsArtinianRing (B ⧸ maximalIdeal B ^ k) := by sorry
