-- Prove2me | Theorems.Thm_GlobalTheory_minor_smul_eq_rowSpace_of_cofVec_orth
-- name    : GlobalTheory.minor_smul_eq_rowSpace_of_cofVec_orth
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:18:03.952963+00:00
-- url     : https://prove2.me/theorems/e5690e72-28f8-4566-aa36-95f82f57ba7e
-- title:
--   Global Theory: minor smul eq row Space of cof Vec orth
-- statement:
--   The Global Theory construction uses the minor smul eq row Space of cof Vec orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MinorSmulEqRowSpaceOfCofVecOrth.lean#L10-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MinorSmulEqRowSpaceOfCofVecOrth.lean#L10-L44

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MinorSmulEqRowSpaceOfCofVecOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.minor_smul_eq_rowSpace_of_cofVec_orth (K V : Type) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (r : ℕ)
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)) (u : Fin (r + 1) → V)
    (hu : ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • u b = 0) (b : Fin (r + 1)) :
    (Y.submatrix id b₀.succAbove).det • u b =
      ∑ a, Y a b • ∑ c, (Y.submatrix id b₀.succAbove).adjugate c a • u (b₀.succAbove c) := by sorry
