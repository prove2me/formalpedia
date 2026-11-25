-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_IntBasis_norm_term
-- name    : GlobalTheory.Cyc.IntBasis.norm_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:14.105812+00:00
-- url     : https://prove2.me/theorems/299649fc-3ce5-45ef-91a1-e4c8fb7265b4
-- title:
--   Int Basis: norm term
-- statement:
--   The Int Basis construction uses the norm term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L30-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L30-L65

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

theorem GlobalTheory.Cyc.IntBasis.norm_term (K : FinExt l) (i : ℕ) (hi : 2 ≤ i) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ i))
    (z : Om l) (hz : z ∈ Ks K (i - 1)) (h0 : z ≠ 0) :
    ∃ n : ℤ, ‖z‖ = (l : ℝ) ^ (((n * l : ℤ) : ℝ) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1))) ∧
      ∀ a : ℕ, ‖z * (ζ - 1) ^ a‖ =
        (l : ℝ) ^ (((n * l - a : ℤ) : ℝ) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1))) := by sorry
