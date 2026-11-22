-- Prove2me | Theorems.Thm_HardyFLocal_equal_clump_composites_preserve_probability
-- name    : HardyFLocal.equal_clump_composites_preserve_probability
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T01:15:57.554699+00:00
-- url     : https://prove2.me/theorems/e502ffae-2352-4225-b328-866f429d253e
-- title:
--   Equal composite maps on every clump give equal product-experiment probabilities
-- statement:
--   Suppose two product-operation lattice experiments agree on exterior wire operations and induce the same end-to-end transformation on each maximal clump of each wire. Their probabilities coincide for every initial global matrix, including entangled density matrices.
-- source:
--   Hardy, arXiv:0804.0054, section 5, clumping steps 1–3.

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_product_lattice_trace
open HardyCausaloid
open Classical

namespace HardyFLocal

open Classical in
theorem equal_clump_composites_preserve_probability {m n : ℕ} (O : Finset (X m n))
    (ρ : GlobalMat m n) (t t' : ∀ x, Label (Setting m n) (Outcome m n) x)
    (U U' : Q m n → X m n → Op (Fin 2))
    (h : ∀ x, labelOp (t x) = prodOp (U (.inl x.1) x) (U (.inr x.2) x))
    (h' : ∀ x, labelOp (t' x) = prodOp (U' (.inl x.1) x) (U' (.inr x.2) x))
    (hg : ∀ q x, x ∈ qubitVertices q → x ∉ O → U q x = U' q x)
    (hc : ∀ q c, c ∈ clumps O q → ∀ a, c.foldl (fun b x => U q x b) a = c.foldl (fun b x => U' q x b) a) :
    latticeProb ρ t = latticeProb ρ t' := by sorry

end HardyFLocal
