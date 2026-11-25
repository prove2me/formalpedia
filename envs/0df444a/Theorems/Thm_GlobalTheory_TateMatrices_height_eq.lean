-- Prove2me | Theorems.Thm_GlobalTheory_TateMatrices_height_eq
-- name    : GlobalTheory.TateMatrices.height_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:46:19.410255+00:00
-- url     : https://prove2.me/theorems/042af303-230d-465e-a7f8-d3a7d2b7533c
-- title:
--   Tate Matrices: height eq
-- statement:
--   The Tate Matrices construction uses the height eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L157-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L157-L195

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

theorem GlobalTheory.TateMatrices.height_eq (Tw : ATower R₀ p) [Algebra ℤ_[p] (Tw.O : Type)] (Dp : ∀ n, DualPair (Tw.R n))
    (gb : Module.Basis (Fin g) R₀ B.gg) (A : OAdj B Tw.O) (M : Matrix (Fin g) (Fin g) (Tw.O : Type))
    (hM : ∀ {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (M k l) * i) →
      A.ab.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))
    {κ : Type} [Fintype κ] (τ : κ → ℕ → B.G Tw.O) (hτ : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (ht : κ → B.gg →ₗ[R₀] (Tw.O : Type))
    (hht : ∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i))
    (j : κ) (c : κ → ℤ_[p])
    (hc : ∀ n, A.a.f (LHom.id Tw.O) (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n)
    (l : Fin g) :
    ∑ k, ht k (gb l) * algebraMap ℤ_[p] (Tw.O : Type) (c k) = ∑ k, M k l * ht j (gb k) := by sorry
