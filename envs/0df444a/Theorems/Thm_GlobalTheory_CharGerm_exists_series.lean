-- Prove2me | Theorems.Thm_GlobalTheory_CharGerm_exists_series
-- name    : GlobalTheory.CharGerm.exists_series
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:49:38.708128+00:00
-- url     : https://prove2.me/theorems/8148d733-bdb9-41a3-b5ef-306a2608b3a1
-- title:
--   Char Germ: exists series
-- statement:
--   The Char Germ construction uses the exists series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSeriesOfTorsionCharacters.lean#L100-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSeriesOfTorsionCharacters.lean#L100-L174

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
variable {R₀ κ : Type} [CommRing R₀]

theorem GlobalTheory.CharGerm.exists_series [Fintype κ] [DecidableEq κ] (p : ℕ)
    [IsPrecomplete (Ideal.span {(p : R₀)}) R₀]
    (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S)
    (hc : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
      (φ : S →ₐ[R₀] S') (a : κ → S), IsNilpotent (p : S) →
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) :
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S) (N : ℕ),
      (p : S) ^ N = 0 → (∀ i, a i ^ N = 0) → c S a = tEval N f a := by sorry
