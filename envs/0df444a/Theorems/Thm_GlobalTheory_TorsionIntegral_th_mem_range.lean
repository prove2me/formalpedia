-- Prove2me | Theorems.Thm_GlobalTheory_TorsionIntegral_th_mem_range
-- name    : GlobalTheory.TorsionIntegral.th_mem_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:19:15.244054+00:00
-- url     : https://prove2.me/theorems/6ecaecc1-7830-4d63-976c-6f52555ff252
-- title:
--   Torsion Integral: th mem range
-- statement:
--   The Torsion Integral construction uses the th mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L297-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L297-L299

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
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
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (z : (TF (R := R) F).left)
variable (hd : ∀ (U : T.left.Opens) (y : T.left), y ∈ U → φ.left z ∈ U)
  (hi : ∀ (U : T.left.Opens), φ.left z ∈ U → Function.Injective (gm φ.left z U))
  (he : ∀ ψ ψ' : T.left ⟶ D.P.A.left, φ.left ≫ ψ = φ.left ≫ ψ' → ψ = ψ')
include hd hi he
variable {J₀ : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι} (hJ₀ : Good D.P.L z J₀)
  (h₀ : ∀ (q : T.left ⟶ D.P.A.left) (y : T.left), q y ∈ D.P.L.U (J₀ (φ.left ≫ q)))
include hJ₀ h₀
omit hd hi he

theorem GlobalTheory.TorsionIntegral.th_mem_range (x x' w : T ⟶ D.P.A) : th D z J₀ (φ ≫ x) (φ ≫ x') (φ ≫ w) ∈ (gm φ.left z ⊤).range := by sorry
