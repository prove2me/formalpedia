-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_exists_energy_min
-- name    : GlobalTheory.ClassFin.exists_energy_min
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:46.802205+00:00
-- url     : https://prove2.me/theorems/4bbc65f6-c009-42e5-97aa-e7254f592566
-- title:
--   Class Fin: exists energy min
-- statement:
--   The Class Fin construction uses the exists energy min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEnergyMin.lean#L63-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEnergyMin.lean#L63-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEnergyMin
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
open GlobalTheory.ClassFin.EnergyMin

theorem GlobalTheory.ClassFin.exists_energy_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), (∀ s, IsUnit (g s).det) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ (P : Matrix ι ι ℂ) (H : σ → Matrix ι ι ℂ), IsUnit P.det ∧ (∀ s, IsLog (H s) ((P * g s * P⁻¹)ᴴ * (P * g s * P⁻¹))) ∧ ∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re := by sorry
