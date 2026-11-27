-- Prove2me | Theorems.Thm_HMBinPacking_integer_feasibility_origin_symmetric
-- name    : HMBinPacking.integer_feasibility_origin_symmetric
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:35:35.88823+00:00
-- url     : https://prove2.me/theorems/93b151c9-7564-5cdc-88e2-9247abbc9048
-- title:
--   Oracle integer feasibility for origin-symmetric convex sets in every dimension
-- statement:
--   Lemma 5 with the single additional hypothesis that Q is symmetric about the origin. The dimension, positive rational radius, precision bound, oracle-answer exponent and strong separation oracle are arbitrary. A single actual oracle-machine execution uses one query and meets both registered bounds.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat encodeRat)

theorem HMBinPacking.integer_feasibility_origin_symmetric :
    ∀ e : ℕ, ∃ (c : ℕ) (OM : OracleMachine),
      ∀ n : ℕ, 1≤n → ∀ T : ℚ, 1≤T → ∀ σ : ℕ, n+enc T≤σ →
      ∀ Q : Set (Fin n→ℝ), IsClosed Q → Convex ℝ Q → (∀ x∈Q,∀ i,|x i|≤(T:ℝ)) →
      (∀ x∈Q,-x∈Q) → ∀ O : List Bool→List Bool,
        (∀ y : Fin n→ℚ, IsSepAnswer Q y (O (encVec y)) ∧ (O (encVec y)).length≤(σ+(encVec y).length)^e) →
        ∃ w : List Bool, ORunsWithin OM O (encodeNat n++encodeRat T++encodeNat σ) w
          (2^(c*n^3)*σ^c) (2^(c*n^3)*σ^c) ∧
          ((∃ x : Fin n→ℤ, w=true::encodeIntVec x ∧ zCast x∈Q) ∨
           (w=[false] ∧ ∀ x : Fin n→ℤ,zCast x∉Q)) := by sorry
