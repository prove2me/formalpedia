-- Prove2me | Theorems.Thm_GlobalTheory_ConvFE_conv_famFE
-- name    : GlobalTheory.ConvFE.conv_famFE
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:57:24.794656+00:00
-- url     : https://prove2.me/theorems/39d4bdef-1c7a-4d2e-836f-06973a0b81a6
-- title:
--   Conv FE: conv fam FE
-- statement:
--   The Conv FE construction uses the conv fam FE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalSecScale.lean#L155-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalSecScale.lean#L155-L189

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdicSumRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConvTermFe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RelationOfFiniteLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecScale
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
open GlobalTheory GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.ConvFE.conv_famFE : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W), Function.Injective φ.left.appTop.hom → ∀ (k l : ℕ) (f : ∀ α, SecBT D (TA V W) k α) (g : ∀ α, SecBT D (TA V W) l α) (h : ∀ α, SecBT D (TA V W) (k + l) α) (s : Raw D F k) (s' : Raw D F l) (s'' : Raw D F (k + l)) (a a' : Multiplicative D.X →* Wˣ), (∀ mu : D.X, a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1) → PullB D F φ k f s → PullB D F φ l g s' → PullB D F φ (k + l) h s'' → DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ConvT (IsLocalRing.maximalIdeal V) (twist a f) (twist a' g) h → DegPre.FamFE D F (k + l) s'' := by sorry
