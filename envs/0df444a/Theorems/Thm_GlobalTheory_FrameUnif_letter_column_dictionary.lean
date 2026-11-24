-- Prove2me | Theorems.Thm_GlobalTheory_FrameUnif_letter_column_dictionary
-- name    : GlobalTheory.FrameUnif.letter_column_dictionary
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:36:20.622199+00:00
-- url     : https://prove2.me/theorems/cbaa04d2-6d0b-4662-8b3e-3f1bca27dd53
-- title:
--   Frame Unif: letter column dictionary
-- statement:
--   The Frame Unif construction uses the letter column dictionary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmTypeLetterFrameColumnDictionary.lean#L80-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmTypeLetterFrameColumnDictionary.lean#L80-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.FrameUnif

theorem GlobalTheory.FrameUnif.letter_column_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by sorry
