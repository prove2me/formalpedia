-- Prove2me | Theorems.Thm_GlobalTheory_ThetaAmple_relAmple_of_values
-- name    : GlobalTheory.ThetaAmple.relAmple_of_values
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:13.389825+00:00
-- url     : https://prove2.me/theorems/ad4a6bf8-62ff-48eb-b920-153efe9c8bc8
-- title:
--   Theta Ample: rel Ample of values
-- statement:
--   The Theta Ample construction uses the rel Ample of values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L75-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L75-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple

theorem GlobalTheory.ThetaAmple.relAmple_of_values
    (hext : ∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens)
      (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U →
        valAt' x.left U f = valAt' x.left U f') → f = f')
    {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {L : LB X.left} (hL : L.IsLB)
    {Z κ : Type} [Fintype κ] [Nonempty κ] (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (hex : Function.Surjective ex)
    (fr : L.ι → Z → ℂ) (fr_ne : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → fr i z ≠ 0)
    (fr_compat : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j) →
      fr i z = valAt' (ex z).left (L.U i ⊓ L.U j) (L.g i j).val * fr j z)
    (f : κ → Z → ℂ) {N : ℕ} (hN : 1 ≤ N)
    (hsec : ∀ c (j : Fin N → L.ι), ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z,
      (∀ k, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U (j k)) →
        ⊤ ≤ (ex z).left ⁻¹ᵁ U ∧ valAt' (ex z).left U φ = f c z * ∏ k, fr (j k) z)
    (D : κ → X.left.Opens) (hcov : ⨆ c, D c = ⊤) (haff : ∀ c, IsAffineOpen (D c))
    (hD : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ f c z ≠ 0) (r : ∀ c, κ → Γ(X.left, D c))
    (hr : ∀ c c' z, f c z ≠ 0 → valAt' (ex z).left (D c) (r c c') = f c' z / f c z)
    (hgen : ∀ c (t : Γ(X.left, D c)), ∃ F : MvPolynomial κ ℂ, t = MvPolynomial.eval₂
      (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r c) F) :
    Out.RelAmple X L := by sorry
