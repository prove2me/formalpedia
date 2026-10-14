-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_argyros_haydon_scalar_plus_compact
-- name    : InvariantSubspaceProblem.argyros_haydon_scalar_plus_compact
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:26:36.055458+00:00
-- url     : https://prove2.me/theorems/42b25cde-73fe-4582-b837-95b10d917add
-- title:
--   Argyros–Haydon: a scalar-plus-compact Banach space
-- statement:
--   **Theorem (Argyros–Haydon 2011).** There exists a separable, infinite-dimensional real Banach space $E$ on which every bounded linear operator $T\colon E\to E$ has the form
--
--   $$
--   T=\lambda I+K,\qquad \lambda\in\mathbb{R},\ K \text{ compact}.
--   $$
--
--   This solves the scalar-plus-compact problem; it is cited as reference [4] of the source.
--
--   **Formalization Note** The space is existentially quantified (in `Type`). Separability records that the constructed space has a Schauder basis.
-- source:
--   S. A. Argyros & R. G. Haydon, A hereditarily indecomposable L∞-space that solves the scalar-plus-compact problem, Acta Math. 206 (2011) 1–54, arXiv:0903.3921 , main theorem; cited as [4] in Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem argyros_haydon_scalar_plus_compact :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E) (_ : CompleteSpace E),
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional ℝ E ∧
      ∀ T : E →L[ℝ] E, ∃ (c : ℝ) (K : E →L[ℝ] E), IsCompactOperator K ∧ T = c • 1 + K := by sorry

end InvariantSubspaceProblem
