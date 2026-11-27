-- Prove2me | Theorems.Thm_HMBinPacking_integer_feasibility_fixed_box
-- name    : HMBinPacking.integer_feasibility_fixed_box
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:44:47.698796+00:00
-- url     : https://prove2.me/theorems/e8564d94-3c90-52fa-8fc3-7d072a04de8b
-- title:
--   Oracle integer feasibility inside any fixed integer box, with explicit time and query bounds
-- statement:
--   Given an integer H, one oracle machine works for every dimension n, every admissible rational radius T <= H, every precision bound, and every valid strong-separation oracle for any set inside the box. It returns an encoded integer witness or correctly certifies infeasibility. Both the explicit enumeration bound and the registered time and query budget hold. The machine depends on H, and the constant of the registered bound can depend on H and the answer exponent.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Oracles
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat encodeRat)

theorem HMBinPacking.integer_feasibility_fixed_box :
    ∀ H : ℕ, ∃ OM : OracleMachine, ∀ e : ℕ, ∃ c : ℕ,
      ∀ n : ℕ, 1≤n → ∀ T : ℚ, 1≤T → T≤H → ∀ σ : ℕ, n+enc T≤σ →
      ∀ Q : Set (Fin n→ℝ), (∀ x∈Q,∀ i,|x i|≤(T:ℝ)) → ∀ O : List Bool→List Bool,
       (∀ y : Fin n→ℚ,IsSepAnswer Q y (O (encVec y)) ∧ (O (encVec y)).length≤(σ+(encVec y).length)^e) →
       let raw:=encodeNat n++encodeRat T++encodeNat σ
       let q:=n*(2*H.size+5)
       let t:=1+100*(raw.length+n+2)^2+(2*H+1)^n*(6*n+2*(n*(2*H.size+2))+(σ+q)^e+12)
       let B:=2^(c*n^3)*σ^c
       ∃ w : List Bool, ORunsWithin OM O raw w (min t B) (min q B) ∧
         ((∃ x : Fin n→ℤ,w=true::encodeIntVec x ∧ zCast x∈Q) ∨
          (w=[false] ∧ ∀ x : Fin n→ℤ,zCast x∉Q)) := by sorry
