-- Prove2me | Theorems.Thm_GlobalTheory_UnifParts_cls_eq
-- name    : GlobalTheory.UnifParts.cls_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:05.182871+00:00
-- url     : https://prove2.me/theorems/9362c385-4fe6-41a4-bb7c-113579c0b382
-- title:
--   Unif Parts: cls eq
-- statement:
--   The Unif Parts construction uses the cls eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FamilyUnifOfParts.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FamilyUnifOfParts.lean#L156-L158

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (perObj : ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), InGenus D l σ D' t →
    IsPeriod D' ty P → ∃ y e, Unif Xo σ ty D' t P y e)
  (upUniq : ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t' : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ))
    (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.X) e e', Unif Xo σ ty D' t P y e → Unif Xo σ ty D'' t' P' y' e' →
    (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞 E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, D''.EF (gam a) (gam b) = D'.EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧
      (∀ a, ∃ x, gam (t a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a)))
include perObj upUniq

theorem GlobalTheory.UnifParts.cls_eq {y y' : Sp ℂ ⟶ Xo.X} {x} (hx : x ∈ cls Xo σ ty y) (hx' : x ∈ cls Xo σ ty y') :
    cls Xo σ ty y = cls Xo σ ty y' := by sorry
