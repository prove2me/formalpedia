-- Prove2me | Theorems.Thm_GlobalTheory_MixedSignature_finite_types
-- name    : GlobalTheory.MixedSignature.finite_types
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:07.718605+00:00
-- url     : https://prove2.me/theorems/bbf935f7-38f6-45c1-b88b-e04314c70a4d
-- title:
--   Mixed Signature: finite types
-- statement:
--   The Mixed Signature construction uses the finite types property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBoundOrthonormalFrame.lean#L368-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBoundOrthonormalFrame.lean#L368-L385

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBoundOrthonormalFrame
import Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
import Theorems.Thm_GlobalTheory_FlagMahler_col_map_eq
import Theorems.Thm_GlobalTheory_FlagMahler_comb_bound
import Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
import Theorems.Thm_GlobalTheory_FlagMahler_finite_int_sq
import Theorems.Thm_GlobalTheory_FlagMahler_finite_types
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

theorem GlobalTheory.MixedSignature.finite_types {ι : Type} [Fintype ι] [DecidableEq ι] (p : X.Ψ → ℕ) {den : 𝓞 E} (hden : den ≠ 0)
    (hint : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (C D : ℝ) (hD : 0 ≤ D) :
    (basisType X G '' {f : Basis ι ℤ X.Λ | ∃ y, Normal X G p y ∧
      (∀ i, QuadraticLatticeForms.Qy X y (f i) ≤ C) ∧
      ∀ (v : X.Λ) (i : ι), ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ D * QuadraticLatticeForms.Qy X y v}).Finite := by sorry
