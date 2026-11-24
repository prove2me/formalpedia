-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_mem_of_pos
-- name    : GlobalTheory.UnitLemma.Desc.Window.mem_of_pos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:07.494571+00:00
-- url     : https://prove2.me/theorems/a7c91855-6d17-4a52-9b5b-64ac695334b5
-- title:
--   Window: mem of pos
-- statement:
--   The Window construction uses the mem of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L183-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L183-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem GlobalTheory.UnitLemma.Desc.Window.mem_of_pos {a : K.O} (ha : K.Small a) [Fintype ι] {e : ι → B.A} {N : ℕ} {M : Submodule K.O B.A}
    {p : ι → ℤ} (hP : Pos B a e N M p) (i : ι) {c : ℕ} {y : B.A}
    (hy : ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y)) (k : ℕ) (hk : p i + N + c ≤ 2 * k) :
    e i * (al K a ^ ((2 * k : ℕ) : ℤ) • y) ∈ M := by sorry
