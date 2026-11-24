-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_smul_vecMul_mem
-- name    : GlobalTheory.BoundedBasis.smul_vecMul_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:01:28.297306+00:00
-- url     : https://prove2.me/theorems/26bda929-de33-4a49-9a33-4f94635f8487
-- title:
--   Bounded Basis: smul vec Mul mem
-- statement:
--   The Bounded Basis construction uses the smul vec Mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L250-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L250-L254

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

theorem GlobalTheory.BoundedBasis.smul_vecMul_mem {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L') (o : Fin r → 𝓞 E) :
    (X.NC : E) • ((fun i => (o i : E)) ᵥ* Matrix.of v) ∈ X.Λ := by sorry
