-- Prove2me | Theorems.Thm_GlobalTheory_ZH_ConePrime_vanishingIdeal_eq_ker
-- name    : GlobalTheory.ZH.ConePrime.vanishingIdeal_eq_ker
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:02:07.308312+00:00
-- url     : https://prove2.me/theorems/1b2faa05-cf4a-438a-bca5-c8ae336a6cc0
-- title:
--   Cone Prime: vanishing Ideal eq ker
-- statement:
--   The Cone Prime construction uses the vanishing Ideal eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L218-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L218-L264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k : Type} [Field k] {X : Scheme.{0}}
variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem GlobalTheory.ZH.ConePrime.vanishingIdeal_eq_ker [IsAlgClosed k] [Fintype J] [IsIntegral X] (p : X ⟶ Sp k) (hH : H.IsLB) {J₀ : Set J}
    (him : ImmBy p H s J₀) (i : J) (haff : IsAffineOpen (Out.nonzeroLocus (s i)))
    (hne : ((Out.nonzeroLocus (s i) : X.Opens) : Set X).Nonempty)
    (r : J → Γ(X, Out.nonzeroLocus (s i))) (hr : ∀ j, IsRatio (s j) (s i) _ (r j))
    (hc : Subring.closure (Set.range (constFn p (Out.nonzeroLocus (s i))) ∪ Set.range r) = ⊤) :
    MvPolynomial.vanishingIdeal k (cone p H s) = RingHom.ker (coneHom (constHom p _) r) := by sorry
