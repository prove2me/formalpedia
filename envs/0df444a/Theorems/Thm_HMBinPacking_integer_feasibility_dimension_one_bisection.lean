-- Prove2me | Theorems.Thm_HMBinPacking_integer_feasibility_dimension_one_bisection
-- name    : HMBinPacking.integer_feasibility_dimension_one_bisection
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:21:21.824671+00:00
-- url     : https://prove2.me/theorems/0b32acde-78e4-498c-be96-73362568c3da
-- title:
--   Oracle integer feasibility in dimension one for every rational radius
-- statement:
--   A single actual oracle machine satisfies the registered integer-feasibility witness, time, and query-length specification for all admissible rational radii in dimension one and every strong-separation oracle and answer exponent. It also meets the explicit bounds t and q in the statement. No symmetry hypothesis is required.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib.Tactic.Linarith
import Definitions.Def_HMBinPacking_OutputsWithin
import Mathlib.Tactic.FinCases
import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Positivity
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_HMBinPacking_Oracles
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith.Frontend
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat encodeRat)

theorem HMBinPacking.integer_feasibility_dimension_one_bisection :
    ∃ OM:OracleMachine,∀ e:ℕ,∀ T:ℚ,1≤T → ∀ σ:ℕ,1+enc T≤σ →
      ∀ Q:Set (Fin 1→ℝ),(∀x∈Q,∀i,|x i|≤(T:ℝ)) → ∀ O:List Bool→List Bool,
      (∀y:Fin 1→ℚ,IsSepAnswer Q y (O (encVec y)) ∧ (O (encVec y)).length≤(σ+(encVec y).length)^e) →
      let raw:=encodeNat 1++encodeRat T++encodeNat σ
      let m:=T.num.natAbs.size+1-T.den.size
      let q:=2*m+5
      let t:=200*(raw.length+3)^2+(m+5)*(60*(m+1)+(σ+q)^e+30)
      let c:=3*e+24
      let B:=2^c*σ^c
      ∃w:List Bool,ORunsWithin OM O raw w (min t B) (min q B) ∧
         ((∃x:Fin 1→ℤ,w=true::encodeIntVec x ∧ zCast x∈Q) ∨ (w=[false] ∧ ∀x:Fin 1→ℤ,zCast x∉Q)) := by sorry
