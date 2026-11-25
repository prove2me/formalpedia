-- Prove2me | Theorems.Thm_GlobalTheory_isLocalHom_integralClosureToPadicAlgClIntegers
-- name    : GlobalTheory.isLocalHom_integralClosureToPadicAlgClIntegers
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:44:14.441198+00:00
-- url     : https://prove2.me/theorems/7143ac32-9abe-464a-8388-869505c13d1f
-- title:
--   Global Theory: is Local Hom integral Closure To Padic Alg Cl Integers
-- statement:
--   The Global Theory construction uses the is Local Hom integral Closure To Padic Alg Cl Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L34-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.isLocalHom_integralClosureToPadicAlgClIntegers
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsLocalHom (integralClosureToPadicAlgClIntegers K) := by sorry
