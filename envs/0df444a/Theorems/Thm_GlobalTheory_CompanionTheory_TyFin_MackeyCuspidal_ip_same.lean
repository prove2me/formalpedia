-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_ip_same
-- name    : GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.ip_same
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:34:48.653869+00:00
-- url     : https://prove2.me/theorems/88b08192-38c8-4d6e-a90e-2d5226e9c51f
-- title:
--   Mackey Cuspidal: ip same
-- statement:
--   The Mackey Cuspidal construction uses the ip same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyFormulaAll.lean#L128-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyFormulaAll.lean#L128-L147

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s s' : ℕ}
open Classical

theorem GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.ip_same (b : ι → Fin s) (π : Fin s ≃ Fin s') (β : ι → Fin s') (hβ : β = π ∘ b) (b' : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
    (e : ∀ c : Fin s', {i // β i = c} ≃ {j // b' j = c})
    (hl : ∀ c, Simple (lam c)) (hm : ∀ c, Simple (mu c)) :
    ip ((parab K b ⊓ parab K β : Subgroup (GL ι K)) : Set (GL ι K))
      (hcFun b fun c => (lam c).character)
      (hcFun β fun c x => (mu c).character (glEquiv K (e c) x)) =
      if ∀ c, CuspIso K (lam c) (mu (π c)) then 1 else 0 := by sorry
