-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_read_counterexample_l1
-- name    : InvariantSubspaceProblem.read_counterexample_l1
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:25:54.324011+00:00
-- url     : https://prove2.me/theorems/80e2f968-acfb-4d38-ae72-532fed5dee9c
-- title:
--   Read: an operator on ℓ¹ without closed invariant subspaces
-- statement:
--   **Theorem (Read 1985).** There is a bounded linear operator $T$ on the complex sequence space
--
--   $$
--   \ell^1(\mathbb{N})=\Big\{(a_n)_{n\ge 0}\subseteq\mathbb{C} : \sum_n |a_n|<\infty\Big\}
--   $$
--
--   that has no non-trivial closed invariant subspace.
--
--   This gives a counterexample on a classical Banach space, in contrast with Enflo's specially constructed space.
--
--   **Formalization Note** $\ell^1$ is Mathlib's `lp (fun _ : ℕ => ℂ) 1` with its usual norm.
-- source:
--   C. J. Read, A solution to the invariant subspace problem on the space l1, Bull. London Math. Soc. 17 (1985) 305–317, https://doi.org/10.1112/blms/17.4.305 , main theorem.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem read_counterexample_l1 :
    ∃ T : lp (fun _ : ℕ => ℂ) 1 →L[ℂ] lp (fun _ : ℕ => ℂ) 1,
      ¬ HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
