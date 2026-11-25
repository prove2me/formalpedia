-- Prove2me | Theorems.Thm_GlobalTheory_TateMatrices_eq_of_zeta_pow
-- name    : GlobalTheory.TateMatrices.eq_of_zeta_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:46:54.451524+00:00
-- url     : https://prove2.me/theorems/5888ac4f-fd5b-4059-94a5-5fc6285ee50e
-- title:
--   Tate Matrices: eq of zeta pow
-- statement:
--   The Tate Matrices construction uses the eq of zeta pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L117-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L117-L129

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
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.TateMatrices.eq_of_zeta_pow {G : Type} [CommGroup G] {κ : Type} [Fintype κ] (ζ : ℕ → G)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (p ^ (n + 1))) (a b c d : κ → ℤ_[p])
    (h : ∀ n, ζ n ^ (∑ k, (PadicInt.toZModPow (n + 1) (a k)).val * (PadicInt.toZModPow (n + 1) (b k)).val) =
      ζ n ^ (∑ k, (PadicInt.toZModPow (n + 1) (c k)).val * (PadicInt.toZModPow (n + 1) (d k)).val)) :
    ∑ k, a k * b k = ∑ k, c k * d k := by sorry
