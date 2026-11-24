-- Prove2me | Theorems.Thm_GlobalTheory_FrameFibre_lact_mem_GG
-- name    : GlobalTheory.FrameFibre.lact_mem_GG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:20.243773+00:00
-- url     : https://prove2.me/theorems/db1556d5-eeec-4f54-9356-9431d48335c8
-- title:
--   Frame Fibre: lact mem GG
-- statement:
--   The Frame Fibre construction uses the lact mem GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLevelBlockOfEq.lean#L116-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLevelBlockOfEq.lean#L116-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
variable [IsCMField E]

theorem GlobalTheory.FrameFibre.lact_mem_GG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {q : ℕ} {γ : GL (Fin r) E}
    (hγ : ∀ u v, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      FD.herm G u v) {x : FD.Frame Ψ r} (hx : x ∈ FD.GG Ψ G q) : FD.lact γ x ∈ FD.GG Ψ G q := by sorry
