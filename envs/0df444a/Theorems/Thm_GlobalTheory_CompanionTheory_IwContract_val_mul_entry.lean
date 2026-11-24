-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_mul_entry
-- name    : GlobalTheory.CompanionTheory.IwContract.val_mul_entry
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:38.375039+00:00
-- url     : https://prove2.me/theorems/f8d186a9-7da8-41ab-8789-71a9fe183125
-- title:
--   Iw Contract: val mul entry
-- statement:
--   The Iw Contract construction uses the val mul entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L21-L27

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
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.CompanionTheory.IwContract.val_mul_entry {A B : Matrix (Fin n) (Fin n) F} {r s : ValueGroupWithZero F}
    (hA : ∀ i j, valuation F (A i j) ≤ r) (hB : ∀ i j, valuation F (B i j) ≤ s) (i j : Fin n) :
    valuation F ((A * B) i j) ≤ r * s := by sorry
