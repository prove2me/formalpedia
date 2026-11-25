-- Prove2me | Theorems.Thm_GlobalTheory_DictPinCompare_isMarkStab_iff
-- name    : GlobalTheory.DictPinCompare.isMarkStab_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:58.374793+00:00
-- url     : https://prove2.me/theorems/48f8c1ff-c6f8-54f4-89d4-205e3bd170e5
-- title:
--   Dict Pin Compare: is Mark Stab iff
-- statement:
--   The Dict Pin Compare construction uses the is Mark Stab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L675-L700
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L675-L700

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DictPinCompare
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

theorem GlobalTheory.DictPinCompare.isMarkStab_iff {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (Fm : FamilyUnif Xo σ' ty) (i : Fin Fm.n)
    (X : Data E r) (φ : (Fm.Di i).La ≃ₗ[𝓞 E] X.Λ) :
    IsMarkStab l X (fun a => φ (Fm.t i a)) ↔ ∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fm.Di i).La), ∃ b : (Fm.Di i).La,
        γ.1 *ᵥ (φ a : Fin r → E) = (φ a : Fin r → E) + (l.M : ℕ) • (φ b : Fin r → E) := by sorry
