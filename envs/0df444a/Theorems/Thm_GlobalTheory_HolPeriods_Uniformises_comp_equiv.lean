-- Prove2me | Theorems.Thm_GlobalTheory_HolPeriods_Uniformises_comp_equiv
-- name    : GlobalTheory.HolPeriods.Uniformises.comp_equiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:31.070011+00:00
-- url     : https://prove2.me/theorems/bbb00f1f-5981-4551-a119-cee6df21b1b8
-- title:
--   Uniformises: comp equiv
-- statement:
--   The Uniformises construction uses the comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsHolToPointAndExp.lean#L33-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsHolToPointAndExp.lean#L33-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsHolToPointAndExp
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
open GlobalTheory GlobalTheory.HolPeriods
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem GlobalTheory.HolPeriods.Uniformises.comp_equiv {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {D' : Datum H}
    {t : D.La →ₗ[𝓞 E] D'.La} {P P' : D'.La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.X}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)} (h : Uniformises Xo σ ty D' t P' y e) (hP : IsPeriod D' ty P)
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ a, P' a = k (P a))
    (hlin : ∀ (a : 𝓞 E) z, k (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * k z i) :
    Uniformises Xo σ ty D' t P y (fun z => e (k z)) := by sorry
