-- Prove2me | Theorems.Thm_GlobalTheory_UU_SchurComp_proportional_raw
-- name    : GlobalTheory.UU.SchurComp.proportional_raw
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:41.459558+00:00
-- url     : https://prove2.me/theorems/7d10699e-4adc-422a-9ca9-fc926c9ff7a8
-- title:
--   Schur Comp: proportional raw
-- statement:
--   The Schur Comp construction uses the proportional raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalRaw.lean#L160-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalRaw.lean#L160-L268

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UU.SchurComp.proportional_raw (hG : GlobalFnsSt) {k : Type} [CommRing k] (iso : k ≃+* F) {A : Type} [CommGroup A] [Finite A]
    {E : Type} [AddCommGroup E] [Module k E] (e : A → A → kˣ) (Φ : A → (E ≃ₗ[k] E))
    (hdim : Module.finrank k E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : kˣ, ∀ v, Φ (a * b) v = (c : k) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : k) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {N : ℕ} (hN0 : N ≠ 0) (m : {g : GtPtF D F // GtTors D N g} → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ N ^ D.rank * Nat.card {g : GtPtF D F // GtTors D N g}) {n : ℕ}
    (hn : N ^ D.rank * n ≤ Module.finrank k E) (x : E → Raw D F N)
    (hlin : ∀ c v v' β j, (x (c • v + v') β).f j = DegPre.constBF D F (iso c) _ * (x v β).f j + (x v' β).f j)
    (hinj : Function.Injective x)
    (hw1 : ∀ χ v, ∃ v', ∀ β, (∃ mu, β = χ + N • mu) ∧ x v' β = x v β ∨
      (¬ ∃ mu, β = χ + N • mu) ∧ ∀ j, (x v' β).f j = 0)
    (hw2 : ∀ χ : D.X, ∃ mu v j, (x v (χ + N • mu)).f j ≠ 0)
    (hw3 : ∀ χ, (∃ v j, (x v χ).f j ≠ 0) → ∀ v, (∀ β, (¬ ∃ mu, β = χ + N • mu) → ∀ j, (x v β).f j = 0) →
      (∀ j, (x v χ).f j = 0) → v = 0)
    (hbas : ∀ β, ∃ b : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε N)),
      ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε N)), ∃ c : Fin n → F,
        ∀ j, s.f j = ∑ i, DegPre.constBF D F (c i) _ * (b i).f j)
    (hphi : ∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
      ∀ v, PhiRaw D F N 0 g.1 w (x v) (x (Φ (m g) v)))
    (α mu : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (hu : u.IsGen)
    (hS : ∃ v j, (x v α).f j ≠ 0) : ∃ a : F, ∀ v z J, Good D.P.L z J → sval (x v (α + N • mu)) (𝟙 _) z J =
      gs (𝟙 _) z ⊤ (DegPre.constBF D F a ⊤) * (sval (x v α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val) := by sorry
