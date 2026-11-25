-- Prove2me | Theorems.Thm_GlobalTheory_DictPinCompare_pins_withGroup
-- name    : GlobalTheory.DictPinCompare.pins_withGroup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:31.848824+00:00
-- url     : https://prove2.me/theorems/991f6edf-ab8e-5e94-9173-372fa552c27c
-- title:
--   Dict Pin Compare: pins with Group
-- statement:
--   The Dict Pin Compare construction uses the pins with Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L718-L730
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L718-L730

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

theorem GlobalTheory.DictPinCompare.pins_withGroup (U : Unf Xo c σ r) (Γ : U.Comp → Subgroup (GL (Fin r) E)) (hle : ∀ k, Γ k ≤ (U.X k).Γ)
    (hidx : ∀ k, ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab (U.X k).Gm (U.X k).Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ k)
    (m : U.Comp → ℕ) (hm : ∀ k, 0 < m k)
    (htr : ∀ k, ∀ ξ ∈ (U.X k).Λ, herm (U.X k).Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
      ∃ γ ∈ Γ k, (γ : Matrix (Fin r) (Fin r) E) = transvMat (U.X k).Gm ξ ((m k : E) * s * (U.X k).κ0))
    (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) :
    let U' : Unf Xo c σ r := ⟨U.Comp, fun k => withGroup (U.X k) (Γ k) (hle k) (hidx k) (m k) (hm k) (htr k), U.un⟩
    ((SidePins fr hT L0 xi0 finHom GfC U' hr Kf x₀ ∧ AdPin F fr hT L0 AA xi0 infHom finHom GQ U' dict x₀ ι₀) ↔
      SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧ AdPin F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀) ∧
    ∀ k (mk : Dw.La → (U.X k).Λ), IsMarkStab l (U.X k) mk → (IsMarkStab l (U'.X k) mk ↔ Γ k = (U.X k).Γ) := by sorry
