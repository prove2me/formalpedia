-- Prove2me | Theorems.Thm_HodgeComputer_Formal_HoldoutCover_piola_contraction
-- name    : HodgeComputer.Formal.HoldoutCover.piola_contraction
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:21:38.719406+00:00
-- url     : https://prove2.me/theorems/4a392cec-46bc-4858-a903-0160199265f7
-- title:
--   Piola contraction identity for directional derivatives
-- statement:
--   Let $K$ be a field, $\iota$ a finite type, and $D, E : \iota \to \operatorname{Der}_{\mathbb{Z}}(K, K)$ derivations related by matrices $M, N \in \operatorname{Mat}_{\iota \times \iota}(K)$ with $N M = I$ and $E_j(z) = \sum_k N_{kj} D_k(z)$. Then for every vector $u : \iota \to K$ and scalar $f \in K$,
--
--   $$\sum_{j \in \iota} \left(\sum_{i \in \iota} \frac{u_i}{\det M} M_{ji}\right) E_j(f) = \frac{1}{\det M} \sum_{i \in \iota} u_i D_i(f).$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/ResidueTransport/PiolaContraction.lean

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Derivation.Basic
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.Formal.HoldoutCover.piola_contraction
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K)
    (M N : Matrix ι ι K) (hNM : N * M = 1)
    (chain : ∀ j z, E j z = ∑ k, N k j * D k z) (u : ι → K) (f : K) :
    (∑ j, (∑ i, (u i / M.det) * M j i) * E j f) =
      (∑ i, u i * D i f) / M.det := by sorry
