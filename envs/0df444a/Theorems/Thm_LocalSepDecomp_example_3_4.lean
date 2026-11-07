-- Prove2me | Theorems.Thm_LocalSepDecomp_example_3_4
-- name    : LocalSepDecomp.example_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:12.981915+00:00
-- url     : https://prove2.me/theorems/1ff9eab9-3501-46fb-bd0c-bc5097791917
-- title:
--   Example 3.4 — efficient distinguishers of two tangles form a bottleneck
-- statement:
--   Let $\tau,\tau'$ be tangles in a graph $G$ that are distinguished by some separation. Then the set
--   $$\beta(\tau,\tau')=\{\{A,B\}:\{A,B\}\text{ distinguishes }\tau\text{ and }\tau'\text{ efficiently}\}$$
--   is a bottleneck in $G$ (of order equal to the minimum order of a separation distinguishing $\tau$ and $\tau'$).
--
--   This is the key example of bottlenecks: it turns a tree of bottlenecks into a tree of tangles.
--
--   Differences from the source:
--   - reading: tangles as in [D25, §12.5] (not defined in the paper) → tangles of some order $k\in\mathbb N$: exactly one orientation of each separation of order $<k$, no three small sides whose induced subgraphs cover $G$ (`IsTangle`); reason: Diestel's definition, which the paper cites; distinguishing and efficiency do not depend on which side is called small
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Example 3.4, p.20

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Example 3.4.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Example 3.4, p.20.
For every pair of distinguishable tangles `τ, τ'` in a graph `G`, the set `β(τ, τ')` of all
separations efficiently distinguishing `τ` and `τ'` is a bottleneck in `G`.

**Formalization Note.** Tangles as in Diestel §12.5 (`IsTangleIn`: a tangle of some order
`k ∈ ℕ`). -/
theorem example_3_4 {V : Type u} (G : SimpleGraph V) (τ τ' : Set (Set V × Set V))
    (hτ : IsTangleIn G τ) (hτ' : IsTangleIn G τ') (hd : IsDistinguishable G τ τ') :
    ∃ k : ℕ, IsBottleneck G k (effDistinguishers G τ τ') := by sorry

end LocalSepDecomp
