-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_inDual_of_pos
-- name    : GlobalTheory.UnitLemma.Desc.Window.inDual_of_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:07.387349+00:00
-- url     : https://prove2.me/theorems/54d71dd0-7eda-490e-b983-af716f878f7e
-- title:
--   Window: in Dual of pos
-- statement:
--   The Window construction uses the in Dual of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L193-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L193-L206

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

theorem GlobalTheory.UnitLemma.Desc.Window.inDual_of_pos {a : K.O} (ha : K.Small a) [Fintype ι] {e : ι → B.A} {N : ℕ} {M : Submodule K.O B.A}
    {p : ι → ℤ} (hP : Pos B a e N M p) (i : ι) {c : ℕ} {y : B.A}
    (hy : ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y)) (hp : (c : ℤ) ≤ p i) :
    InDual B (e i * y) M := by sorry
