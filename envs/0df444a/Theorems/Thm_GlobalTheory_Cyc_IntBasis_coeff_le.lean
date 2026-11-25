-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_IntBasis_coeff_le
-- name    : GlobalTheory.Cyc.IntBasis.coeff_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:35:36.885798+00:00
-- url     : https://prove2.me/theorems/7b9cca5a-8d2b-4d05-a76b-5ee812357e6c
-- title:
--   Int Basis: coeff le
-- statement:
--   The Int Basis construction uses the coeff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L97-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L97-L124

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.IntBasis.coeff_le (K : FinExt l) (i : ℕ) (hi : 2 ≤ i) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ i))
    (z : Om l) (hz : z ∈ Ks K (i - 1)) (a : ℕ) (ha : a < l) (h : ‖z * (ζ - 1) ^ a‖ ≤ 1) :
    ‖z‖ ≤ 1 := by sorry
