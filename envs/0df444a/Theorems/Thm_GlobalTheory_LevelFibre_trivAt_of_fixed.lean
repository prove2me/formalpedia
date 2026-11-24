-- Prove2me | Theorems.Thm_GlobalTheory_LevelFibre_trivAt_of_fixed
-- name    : GlobalTheory.LevelFibre.trivAt_of_fixed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:38.281728+00:00
-- url     : https://prove2.me/theorems/8d776544-5bb4-4382-ad69-7666d2d4dcea
-- title:
--   Level Fibre: triv At of fixed
-- statement:
--   The Level Fibre construction uses the triv At of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L193-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L193-L260

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
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
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

theorem GlobalTheory.LevelFibre.trivAt_of_fixed
    (hPull : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo.X), ∃ o' : Obj D l (baseKA l) (z ≫ Xo.s), Nonempty (ObjMap o' Xo.univ z))
    (hRig : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo.X) (o' : Obj D l (baseKA l) (z ≫ Xo.s)) (m m' : SABMap o'.t Xo.univ.t z),
      (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo₂.X) (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X) (hg : g.InGam l l₂)
    (hρ : Xo₂.LevAut g ρ) (hx : x ≫ ρ.hom = x) : g.TrivAt l₂ := by sorry
