-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_coe_pairing
-- name    : GlobalTheory.BoundedBasis.coe_pairing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:45.7778+00:00
-- url     : https://prove2.me/theorems/f499ffec-1eda-428f-b51b-70e5d3b6c816
-- title:
--   Bounded Basis: coe pairing
-- statement:
--   The Bounded Basis construction uses the coe pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L229-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L229-L233

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

theorem GlobalTheory.BoundedBasis.coe_pairing (v : Fin r → Fin r → E) (hv : ∀ i, v i ∈ X.L') (x : X.Λ) (c : Fin r → E)
    (hc : (x : Fin r → E) = c ᵥ* Matrix.of v) (k : Fin r) :
    ((pairing X v hv x k : 𝓞 E) : E) = (((X.NA : E) • c) ᵥ* gramOf X.Gm v) k := by sorry
