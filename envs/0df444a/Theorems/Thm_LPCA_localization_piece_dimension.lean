-- Prove2me | Theorems.Thm_LPCA_localization_piece_dimension
-- name    : LPCA.localization_piece_dimension
-- status  : Proved
-- author  : @kaiyue
-- created : 2026-10-20T22:44:44.397761+00:00
-- url     : https://prove2.me/theorems/786bffe7-8afa-4223-8cb9-01a07dfe26e2
-- title:
--   Lemma 2.1 — Dimension of localized homogeneous pieces
-- statement:
--   Let $k$ be a field and $\Delta$ a finite downward-closed face family on a finite ambient vertex set $V$. For any $F\subseteq V$ and $a\in\mathbb Z^V$, the actual homogeneous subspace of $k[\Delta]_{x_F}$ is finite dimensional and has dimension
--
--   $$\dim_k(k[\Delta]_{x_F})_a=\begin{cases}1,&a_j\ge0\ (j\notin F)\text{ and }\operatorname{supp}_+(a)\cup F\in\Delta,\\0,&\text{otherwise}.\end{cases}$$
--
--   The homogeneous subspace is defined as the span of actual monomial fractions in the localized polynomial quotient. Void complexes, ghost vertices, and the empty inversion set are included.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Lemma 2.1, Section 2.1.

import Definitions.Def_LPCA
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
universe u

namespace LPCA
theorem localization_piece_dimension
    {V : Type u} [DecidableEq V] [Fintype V]
    (k : Type u) [Field k] (K : Complex V) (F : Finset V) (a : V → ℤ) :
    Module.Finite k (localizedPiece k K F a) ∧
      Module.finrank k (localizedPiece k K F a) =
        (if LocalizationCriterion K F a then 1 else 0) := by sorry
end LPCA
