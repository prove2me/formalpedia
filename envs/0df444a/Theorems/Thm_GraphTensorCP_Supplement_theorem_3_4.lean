-- Prove2me | Theorems.Thm_GraphTensorCP_Supplement_theorem_3_4
-- name    : GraphTensorCP.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:24:23.901211+00:00
-- url     : https://prove2.me/theorems/d2c3334f-9840-4c94-9b50-5479c5697879
-- title:
--   Theorem 3.4 — simultaneous separation of an aligned partial direct sum
-- statement:
--   Let $\mathbb F$ be any field, let $k\ge2$ and $M\ge1$, and let $A$ be the aligned partial direct sum of order-$k$ tensors $A_0,\ldots,A_{M-1}$, sharing coordinates on the first $k-2$ legs and occupying separate sectors on the final two legs. Set
--
--   $$D_{k,M}=1+(k-1)(M-1).$$
--
--   Then the full direct sum of $D_{k,M}$ copies of $A$ formally degenerates to
--
--   $$
--   \bigoplus_{K,h=0}^{M-1}\left(A_h\otimes_K E^{(M)}_{k-1,k}\right).
--   $$
--
--   The direct sum on the right separates every tensor leg. Zero blocks are permitted and retain their specified ambient dimensions.
--
--   This theorem supplies the exact linear-cost simultaneous separation step used by the paper’s entropy inequality.
--
--   **Formalization Note** Legs are 0-based, so the final two legs are `k-2` and `k-1`. `MME.Degenerates X Y` means that the target $X$ degenerates from the source $Y$.
--
--   Differences from the source:
--   - generalization: the source uses coordinate-aligned block inclusions → Lean uses the published invariant predicate `IsAlignedPartialSum`, which also permits transported blocks and zero padding; reason: every source partial sum satisfies the predicate, so the Lean theorem specializes to the printed theorem.
--   - encoding: the source writes $\oplus_K$, $\otimes_K$, and $\rightsquigarrow$ in 1-based coordinates → Lean uses `bigAdd`, `kron`, `Degenerates`, and `Fin k`; reason: these are the corresponding published tensor operations and a change of index base.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 3.4, pp.31–32

import Mathlib
import Definitions.Def_GraphTensorCP_IsAlignedPartialSum
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_mme_degeneration

universe u

namespace GraphTensorCP

namespace Supplement

/-- **Theorem 3.4 (simultaneous separation)**, Zhou, *Asymptotic Rank of Weighted Graph
Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), pp.31–32.
If `A` is an aligned partial direct sum of `M` order-`k` blocks sharing the first `k-2` legs,
then the full direct sum of `D_{k,M}=1+(k-1)(M-1)` copies of `A` degenerates to the full direct
sum of the blocks after each is tensored with an `M`-dimensional edge on the last two legs.

**Formalization Note.** Legs are 0-based, so the paper's `(k-1,k)` are `k-2,k-1` here.
`MME.Degenerates X Y` means the target `X` formally degenerates from the source `Y`. `bigAdd`
is the full direct sum and `kron` the Kronecker product. No nonzero hypothesis is imposed: zero
blocks retain the ambient spaces already stored in the tensor objects. -/
theorem theorem_3_4 {K : Type u} [Field K] {k M : ℕ} (hk : 2 ≤ k) (hM : 1 ≤ M)
    (A : MME.TensorObj K k) (B : Fin M → MME.TensorObj K k)
    (hAB : IsAlignedPartialSum A B) :
    MME.Degenerates
      (MME.TensorObj.bigAdd fun h : Fin M =>
        MME.TensorObj.kron (B h)
          (edgeTensor K ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ M))
      (MME.TensorObj.bigAdd fun _ : Fin (1 + (k - 1) * (M - 1)) => A) := by sorry

end Supplement

end GraphTensorCP
