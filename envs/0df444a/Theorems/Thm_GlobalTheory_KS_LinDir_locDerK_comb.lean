-- Prove2me | Theorems.Thm_GlobalTheory_KS_LinDir_locDerK_comb
-- name    : GlobalTheory.KS.LinDir.locDerK_comb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:03.003474+00:00
-- url     : https://prove2.me/theorems/92a8bc7a-1bf8-4a16-b09e-29c9ee353252
-- title:
--   Lin Dir: loc Der K comb
-- statement:
--   The Lin Dir construction uses the loc Der K comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KsCocLinear.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KsCocLinear.lean#L28-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KsCocLinear
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.LinDir

theorem GlobalTheory.KS.LinDir.locDerK_comb {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D D' : R → K} {c : K} {W₀ : X.Opens} {d d' d'' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h : LocDerK q p m D W₀ d) (h' : LocDerK q p m D' W₀ d')
    (h'' : LocDerK q p m (fun r => c * D r + D' r) W₀ d'') :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d'' W f - constFn q (m ⁻¹ᵁ W) c * d W f - d' W f) := by sorry
