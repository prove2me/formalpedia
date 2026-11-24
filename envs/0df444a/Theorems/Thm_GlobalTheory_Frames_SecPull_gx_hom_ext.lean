-- Prove2me | Theorems.Thm_GlobalTheory_Frames_SecPull_gx_hom_ext
-- name    : GlobalTheory.Frames.SecPull.gx_hom_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:39:12.22482+00:00
-- url     : https://prove2.me/theorems/81814fdc-556d-4915-8471-297c8708b411
-- title:
--   Sec Pull: gx hom ext
-- statement:
--   The Sec Pull construction uses the gx hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueScaledBaseChangeFibreSection.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueScaledBaseChangeFibreSection.lean#L74-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueScaledBaseChangeFibreSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.SecPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem GlobalTheory.Frames.SecPull.gx_hom_ext {S : Type} [CommRing S] {W : Scheme.{0}} {x : Sp S ⟶ Xo.X} (f₁ f₂ : W ⟶ Gx x)
    (h₁ : f₁ ≫ (fst (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : f₁ ≫ (snd (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (snd (Over.mk x) Xo.univ.t.G).left) : f₁ = f₂ := by sorry
