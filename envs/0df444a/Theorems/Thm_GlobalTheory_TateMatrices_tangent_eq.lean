-- Prove2me | Theorems.Thm_GlobalTheory_TateMatrices_tangent_eq
-- name    : GlobalTheory.TateMatrices.tangent_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:36.764969+00:00
-- url     : https://prove2.me/theorems/635f6161-9214-52bb-bb99-1971341c6a1c
-- title:
--   Tate Matrices: tangent eq
-- statement:
--   The Tate Matrices construction uses the tangent eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L137-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L137-L155

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
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀)

theorem GlobalTheory.TateMatrices.tangent_eq {O R : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg) (f : OEnd B O)
    (M : Matrix (Fin g) (Fin g) (O : Type)) (s : LHom O R) (Dp : DualPair R)
    (hM : ∀ (l : Fin g) (i : Dp.π.ker) (m : Fin g → Dp.π.ker),
      (∀ k, (m k : (Dp.D : Type)) = (Dp.σ.comp s).1 (M k l) * i) →
      f.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] i)) =
        B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] m k)) (v : B.gg) :
    f.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap
        (gb.constr R₀ (fun l => ∑ k, gb k ⊗ₜ[R₀] s.1 (M k l)) v)) := by sorry
