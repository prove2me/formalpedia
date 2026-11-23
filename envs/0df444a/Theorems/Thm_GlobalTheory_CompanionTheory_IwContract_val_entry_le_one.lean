-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_entry_le_one
-- name    : GlobalTheory.CompanionTheory.IwContract.val_entry_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:41.41181+00:00
-- url     : https://prove2.me/theorems/2b6bf4ec-bdda-4727-88e7-a36fd3de6f4b
-- title:
--   Iw Contract: val entry le one
-- statement:
--   The Iw Contract construction uses the val entry le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L36-L39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem GlobalTheory.CompanionTheory.IwContract.val_entry_le_one {g : GL (Fin n) F} (hg : g ∈ GlobalTheory.SmGL.iwahori F (Fin n)) (i j : Fin n) :
    valuation F (g.val i j) ≤ 1 := by sorry
