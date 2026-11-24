-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_nuAt_eq_prod
-- name    : GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:11.355019+00:00
-- url     : https://prove2.me/theorems/d34a8cf8-c4c7-4527-80ec-0e3afb7f7bff
-- title:
--   Nu Diag: nu At eq prod
-- statement:
--   The Nu Diag construction uses the nu At eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L62-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L62-L80

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.NuDiag

theorem GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by sorry
