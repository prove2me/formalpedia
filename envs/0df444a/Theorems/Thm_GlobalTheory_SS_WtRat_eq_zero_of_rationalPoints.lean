-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_eq_zero_of_rationalPoints
-- name    : GlobalTheory.SS.WtRat.eq_zero_of_rationalPoints
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:47:22.949401+00:00
-- url     : https://prove2.me/theorems/8a2c902e-d8e9-42d4-9db7-4fa854663aaa
-- title:
--   Wt Rat: eq zero of rational Points
-- statement:
--   The Wt Rat construction uses the eq zero of rational Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusWeightTestGenericPointRationalPoints.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusWeightTestGenericPointRationalPoints.lean#L34-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat

theorem GlobalTheory.SS.WtRat.eq_zero_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {P : Over (Sp k)}
    [Smooth P.hom] {W : P.left.Opens} (d : Γ(P.left, W))
    (h : ∀ (z : 𝟙_ (Over (Sp k)) ⟶ P) (x : (𝟙_ (Over (Sp k))).left),
      z.left x ∉ P.left.basicOpen d) : d = 0 := by sorry
