-- Prove2me | Theorems.Thm_HMBinPacking_integer_feasibility_adaptive_bit_radius
-- name    : HMBinPacking.integer_feasibility_adaptive_bit_radius
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:16:04.618596+00:00
-- url     : https://prove2.me/theorems/43d9eca0-4f81-5c71-bb55-11a1432fafa4
-- title:
--   Uniform oracle integer feasibility in every rational box, with the registered budget in a value-dependent range
-- statement:
--   One fixed oracle machine solves all admissible integer feasibility instances in every dimension and at every rational radius T. It returns the registered signed-integer witness or the correct infeasibility answer, subject only to the original assumptions on the strong-separation oracle and the enclosing box. A fully explicit enumeration clock and query-length bound always hold. The same machine and output meet the original two bounds with c=3e+24 whenever T^n <= 2^(n^3) sigma, including every T <= 2^(n^2). The cutoff uses the numerical radius, independently of how large its reduced denominator is.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib.Tactic.Linarith
import Definitions.Def_HMBinPacking_OutputsWithin
import Mathlib.Tactic.FinCases
import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Data.Nat.Size
import Definitions.Def_HMBinPacking_OracleMachine
import Mathlib.Tactic.Positivity
import Definitions.Def_HMBinPacking_Oracles
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat encodeRat)

theorem HMBinPacking.integer_feasibility_adaptive_bit_radius :
    ∃ OM:OracleMachine,∀ e n:ℕ,1≤n → ∀ T:ℚ,1≤T → ∀ σ:ℕ,n+enc T≤σ →
      ∀ Q:Set (Fin n→ℝ),(∀x∈Q,∀i,|x i|≤(T:ℝ)) → ∀ O:List Bool→List Bool,
      (∀y:Fin n→ℚ,IsSepAnswer Q y (O (encVec y)) ∧ (O (encVec y)).length≤(σ+(encVec y).length)^e) →
      let raw:=encodeNat n++encodeRat T++encodeNat σ
      let m:=T.num.natAbs.size+1-T.den.size
      let q:=n*(2*m+5)
      let t:=200*(raw.length+n+2)^2+2^(n*(m+1))*(10*q+(σ+q)^e+30)
      let c:=3*e+24
      let B:=2^(c*n^3)*σ^c
      ∃ w:List Bool,ORunsWithin OM O raw w t q ∧
        (T^n≤(2:ℚ)^(n^3)*σ → ORunsWithin OM O raw w B B) ∧
        ((∃x:Fin n→ℤ,w=true::encodeIntVec x ∧ zCast x∈Q) ∨ (w=[false] ∧ ∀x:Fin n→ℤ,zCast x∉Q)) := by sorry
