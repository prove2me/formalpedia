-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_rootExchangeParabolic_and_fourierJacobi_iff_entries
-- name    : GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:54.621978+00:00
-- url     : https://prove2.me/theorems/913f2bbf-3aa3-4c22-a45c-96c51e5946a1
-- title:
--   T: mem root Exchange Parabolic and fourier Jacobi iff entries
-- statement:
--   The T construction uses the mem root Exchange Parabolic and fourier Jacobi iff entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntriStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntriStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntriStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by sorry
