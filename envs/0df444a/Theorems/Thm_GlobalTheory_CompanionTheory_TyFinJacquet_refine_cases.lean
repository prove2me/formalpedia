-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_cases
-- name    : GlobalTheory.CompanionTheory.TyFinJacquet.refine_cases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:20.990662+00:00
-- url     : https://prove2.me/theorems/9922f866-15da-491d-86cc-9886dcf84713
-- title:
--   Ty Fin Jacquet: refine cases
-- statement:
--   The Ty Fin Jacquet construction uses the refine cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L187-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L187-L197

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinJacquet
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
variable (b : ι → Fin s) (c : Fin s) {t : ℕ} (b₁ : {i // b i = c} → Fin t) (ht : 1 ≤ t)

theorem GlobalTheory.CompanionTheory.TyFinJacquet.refine_cases (i : ι) :
    ((b i : ℕ) < c ∧ (refine b c b₁ ht i : ℕ) = b i) ∨
    ((b i : ℕ) = c ∧ (c : ℕ) ≤ refine b c b₁ ht i ∧ (refine b c b₁ ht i : ℕ) < c + t) ∨
    ((c : ℕ) < b i ∧ (refine b c b₁ ht i : ℕ) = b i + t - 1) := by sorry
