-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_siegel_cover
-- name    : GlobalTheory.ClassFin.siegel_cover
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:06.141073+00:00
-- url     : https://prove2.me/theorems/fb49d272-fb7f-411c-91e1-65a61c08f407
-- title:
--   Class Fin: siegel cover
-- statement:
--   The Class Fin construction uses the siegel cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SiegelCover.lean#L174-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SiegelCover.lean#L174-L187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SiegelCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
open Matrix
open scoped Kronecker ComplexOrder TensorProduct

theorem GlobalTheory.ClassFin.siegel_cover (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, _root_.GlobalTheory.ClassFin.IsSiegel C k a n ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by sorry
