-- Prove2me | Theorems.Thm_GlobalTheory_MixedSignature_norm_lact_le
-- name    : GlobalTheory.MixedSignature.norm_lact_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:44.452679+00:00
-- url     : https://prove2.me/theorems/9fd091fa-060d-4539-849a-97eea36fd28c
-- title:
--   Mixed Signature: norm lact le
-- statement:
--   The Mixed Signature construction uses the norm lact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBoundOrthonormalFrame.lean#L392-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBoundOrthonormalFrame.lean#L392-L429

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBoundOrthonormalFrame
import Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
import Theorems.Thm_GlobalTheory_FlagMahler_col_map_eq
import Theorems.Thm_GlobalTheory_FlagMahler_comb_bound
import Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
import Theorems.Thm_GlobalTheory_FlagMahler_finite_int_sq
import Theorems.Thm_GlobalTheory_FlagMahler_inv_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_phi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Am_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ipB_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_quad_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MixedSignature
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module Complex
open Matrix hiding col gram
open scoped ComplexConjugate
open QuadraticLatticeForms (ip ipB ipB_apply Ly Am Qy Ly_injective Ly_surjective quad_int Am_posDef)
open HermitianLatticeMaps (phi phi_f phi_zsum phi_mem phi_phi smul_coe coe_expand mulQ mulQ_apply)
open GlobalTheory.FlagMahler (col_map_eq inv_lact comp_le_Qy comb_bound Qy_smul_le finite_int_sq)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ}

theorem GlobalTheory.MixedSignature.norm_lact_le (hG : G.det ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι] {C : ℝ} {f g : Basis ι ℤ X.Λ}
    {w : Frame X.Ψ r} (hw : Normal X G p (mat w)) (hf : ∀ i, QuadraticLatticeForms.Qy X (mat w) (f i) ≤ C)
    {γ : GL (Fin r) E} (hγ : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X g).repr v i • (f i : Fin r → E)) (hs : IsUStab G X.Λ γ)
    (τ : X.Ψ) (l b : Fin r) : ‖lact γ w τ l b‖ ≤ bound X G C g := by sorry
