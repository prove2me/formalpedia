-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_parts
-- name    : GlobalTheory.CompanionTheory.TyFinJacquet.refine_parts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:21.431875+00:00
-- url     : https://prove2.me/theorems/957cfe27-8388-4618-ab89-91623b77792e
-- title:
--   Ty Fin Jacquet: refine parts
-- statement:
--   The Ty Fin Jacquet construction uses the refine parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L234-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L234-L262

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

theorem GlobalTheory.CompanionTheory.TyFinJacquet.refine_parts {u : GL ι K} (hu : u ∈ unip K (refine b c b₁ ht)) :
    ∃ hp : u ∈ parab K b, (∀ c', c' ≠ c → levi K b c' ⟨u, hp⟩ = 1) ∧ levi K b c ⟨u, hp⟩ ∈ unip K b₁ := by sorry
