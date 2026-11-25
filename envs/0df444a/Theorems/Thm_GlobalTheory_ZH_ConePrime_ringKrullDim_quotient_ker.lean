-- Prove2me | Theorems.Thm_GlobalTheory_ZH_ConePrime_ringKrullDim_quotient_ker
-- name    : GlobalTheory.ZH.ConePrime.ringKrullDim_quotient_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:02:18.920213+00:00
-- url     : https://prove2.me/theorems/1c9e6ec5-94ca-461d-bd18-a575069215e6
-- title:
--   Cone Prime: ring Krull Dim quotient ker
-- statement:
--   The Cone Prime construction uses the ring Krull Dim quotient ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L107-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L107-L145

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

theorem GlobalTheory.ZH.ConePrime.ringKrullDim_quotient_ker {k J A : Type} [Field k] [Fintype J] [CommRing A] [IsDomain A] [Algebra k A]
    (r : J → A) (i : J) (hi : r i = 1)
    (h : Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) = ⊤) (g : ℕ) (hg : ringKrullDim A = g) :
    ringKrullDim (MvPolynomial J k ⧸ RingHom.ker (coneHom (algebraMap k A) r)) = (g + 1 : ℕ) := by sorry
