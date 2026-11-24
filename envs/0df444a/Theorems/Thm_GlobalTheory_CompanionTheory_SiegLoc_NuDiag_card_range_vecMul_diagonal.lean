-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_card_range_vecMul_diagonal
-- name    : GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:06.119586+00:00
-- url     : https://prove2.me/theorems/f60a8208-dba8-4a00-995c-caab9b839438
-- title:
--   Nu Diag: card range vec Mul diagonal
-- statement:
--   The Nu Diag construction uses the card range vec Mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L47-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L47-L60

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

theorem GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal {A : Type} [CommRing A] {n : ℕ} (e : Fin n → A) :
    Nat.card (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      ∏ i : Fin n, Nat.card (Set.range fun w : A => w * e i) := by sorry
