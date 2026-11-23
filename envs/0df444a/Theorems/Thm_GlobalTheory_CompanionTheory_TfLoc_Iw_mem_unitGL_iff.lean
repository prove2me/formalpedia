-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_mem_unitGL_iff
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:29.211801+00:00
-- url     : https://prove2.me/theorems/141c6bce-c22a-4c26-a23f-4de1243a78bd
-- title:
--   Iw: mem unit GL iff
-- statement:
--   The Iw construction uses the mem unit GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L13-L38

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff (g : GL (Fin m) F) :
    g ∈ unitGL (n := Fin m) F ↔
      (∀ i j, valuation F ((g : Matrix (Fin m) (Fin m) F) i j) ≤ 1) ∧
      (∀ i j, valuation F (((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j) ≤ 1) := by sorry
