-- Prove2me | Theorems.Thm_GlobalTheory_TateMatrices_pairing_sum_left
-- name    : GlobalTheory.TateMatrices.pairing_sum_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:36.669206+00:00
-- url     : https://prove2.me/theorems/e0d84da9-256c-484f-bfa0-56ee1d2d3acf
-- title:
--   Tate Matrices: pairing sum left
-- statement:
--   The Tate Matrices construction uses the pairing sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L40-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

theorem GlobalTheory.TateMatrices.pairing_sum_left {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (ζ : (R : Type)ˣ) (a e : ι → ℕ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (ζ ^ e i)) :
    B.IsPairing N (∑ i ∈ s, a i • x i) y (ζ ^ ∑ i ∈ s, a i * e i) := by sorry
