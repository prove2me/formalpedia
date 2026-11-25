-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_exists_conj_harm_of_span
-- name    : GlobalTheory.ClassFin.exists_conj_harm_of_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:31.511372+00:00
-- url     : https://prove2.me/theorems/bb910577-5491-4f32-84dc-ed65dde08b94
-- title:
--   Class Fin: exists conj harm of span
-- statement:
--   The Class Fin construction uses the exists conj harm of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsConjHarmOfSpan.lean#L294-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsConjHarmOfSpan.lean#L294-L421

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEnergyMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SumHermitianLogGramEqZeroOfEnergyMinimum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsConjHarmOfSpan
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
open Matrix Polynomial
open scoped Kronecker ComplexOrder TensorProduct

theorem GlobalTheory.ClassFin.exists_conj_harm_of_span : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ P : Matrix ι ι ℂ, IsUnit P.det ∧ _root_.GlobalTheory.ClassFin.Harm (fun s => P * g s * P⁻¹) := by sorry
