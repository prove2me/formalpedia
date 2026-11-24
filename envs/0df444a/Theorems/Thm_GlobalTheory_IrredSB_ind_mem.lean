-- Prove2me | Theorems.Thm_GlobalTheory_IrredSB_ind_mem
-- name    : GlobalTheory.IrredSB.ind_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:20:43.233507+00:00
-- url     : https://prove2.me/theorems/61e1a132-0793-4da9-b27f-1c511b2929ca
-- title:
--   Irred SB: ind mem
-- statement:
--   The Irred SB construction uses the ind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L25-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L25-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {G : Type} [AddCommGroup G]

theorem GlobalTheory.IrredSB.ind_mem {B : Type} (e : B → G → ℂ) (he : ∀ b t u, e b (t + u) = e b t * e b u)
    (W : Submodule ℂ (G → ℂ)) (hM : ∀ Φ ∈ W, ∀ b, (fun t => e b t * Φ t) ∈ W) (K : AddSubgroup G)
    (hsep : ∀ p ∉ K, ∃ b, (∀ u ∈ K, e b u = 1) ∧ e b p ≠ 1) {f : G → ℂ} (hf : f ∈ W)
    (h1 : ∀ u ∈ K, f u = 1) (P : Finset G) (hP : ∀ t, f t ≠ 0 → ∃ p ∈ P, ∃ u ∈ K, t = p + u) :
    ind K ∈ W := by sorry
