-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_term_same
-- name    : GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.term_same
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:33:36.900393+00:00
-- url     : https://prove2.me/theorems/4163fbcf-a627-4ff5-b8e2-fae564912224
-- title:
--   Mackey Cuspidal: term same
-- statement:
--   The Mackey Cuspidal construction uses the term same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyFormulaAll.lean#L175-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyFormulaAll.lean#L175-L188

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocksStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUniqueStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProductStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProductStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIsoStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProductStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatementStatement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyFormulaAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {n s s' : ℕ} (b : Fin n → Fin s) (b' : Fin n → Fin s')
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
  (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
open Classical

theorem GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.term_same (σ : Equiv.Perm (Fin n)) (π : Fin s ≃ Fin s') (h : b' ∘ σ = π ∘ b)
    (hl : ∀ c, Simple (lam c)) (hm : ∀ c, Simple (mu c)) :
    ip ((parab K b ⊓ cj (pm K σ) (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K))
      (hcFun b fun c => (lam c).character)
      (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) =
      if ∀ c, CuspIso K (lam c) (mu (π c)) then 1 else 0 := by sorry
