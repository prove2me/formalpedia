-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_IntBasis_term_le
-- name    : GlobalTheory.Cyc.IntBasis.term_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:48.909801+00:00
-- url     : https://prove2.me/theorems/4d7a8aa1-7f48-40a9-81c6-15afb45f4dda
-- title:
--   Int Basis: term le
-- statement:
--   The Int Basis construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L67-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L67-L95

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

theorem GlobalTheory.Cyc.IntBasis.term_le (K : FinExt l) (i : ℕ) (hi : 2 ≤ i) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ i))
    (z : ℕ → Om l) (hz : ∀ a, z a ∈ Ks K (i - 1)) (a : ℕ) (ha : a < l) :
    ‖z a * (ζ - 1) ^ a‖ ≤ ‖∑ b ∈ Finset.range l, z b * (ζ - 1) ^ b‖ := by sorry
