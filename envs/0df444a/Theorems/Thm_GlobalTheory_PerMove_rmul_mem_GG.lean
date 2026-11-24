-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_rmul_mem_GG
-- name    : GlobalTheory.PerMove.rmul_mem_GG
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:12.41669+00:00
-- url     : https://prove2.me/theorems/e74eae7b-f76c-48cd-8d70-9e8e534fb44c
-- title:
--   Per Move: rmul mem GG
-- statement:
--   The Per Move construction uses the rmul mem GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L184-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L184-L201

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.PerMove.rmul_mem_GG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {q : ℕ}
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G q) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G q := by sorry
