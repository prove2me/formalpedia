-- Prove2me | Theorems.Thm_HardyFLocal_product_lattice_trace
-- name    : HardyFLocal.product_lattice_trace
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:52:45.230507+00:00
-- url     : https://prove2.me/theorems/93a2ff8a-90b7-436f-b864-51a9b9432eae
-- title:
--   Wire-by-wire probability formula for product operations and arbitrary initial states
-- statement:
--   For any global initial matrix, even an entangled state, the lattice probability of product superoperators is a sum over global matrix units. In each summand, traces factor across wires and each wire independently composes its one-qubit maps in lattice time order.
-- source:
--   Hardy, arXiv:0804.0054, section 5, clumping construction.

import Mathlib
import Definitions.Def_HardyFLocal_Lattice
import Theorems.Thm_HardyFLocal_prodOp_apply_kron
open HardyCausaloid
open Classical

namespace HardyFLocal

open Classical in
theorem product_lattice_trace {m n : ℕ} (ρ : GlobalMat m n)
    (t : ∀ x, Label (Setting m n) (Outcome m n) x) (F G : X m n → Op (Fin 2))
    (h : ∀ x, labelOp (t x) = prodOp (F x) (G x)) :
    latticeProb ρ t = (∑ c, ∑ d, ρ c d * ∏ q : Q m n,
      ((vertexList m n).foldl (fun B x =>
        (if q = .inl x.1 then F x else if q = .inr x.2 then G x else LinearMap.id) B)
        (Matrix.single (c q) (d q) (1 : ℂ))).trace).re := by sorry

end HardyFLocal
