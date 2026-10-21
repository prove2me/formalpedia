-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_prop_3_9
-- name    : NaiveFS.Multinomial.prop_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:33.796788+00:00
-- url     : https://prove2.me/theorems/d5df34bc-2d2b-4e11-a39d-a994379b76f5
-- title:
--   Proposition 3.9, p. 13 — (D) has an optimal solution with at most four nonbinary pairs (xᵢ, zᵢ)
-- statement:
--   Let $f^\pm\in\mathbb R^m$ with $f^\pm_i>0$ and $k<m$. The dual problem (D) of Proposition 3.7 has an optimal solution $(x,z)$, $z=\mathbf 1-x$, such that
--   $$\#\{i:\ x_i\notin\{0,1\}\}\le4.$$
--
--   The bound four is the number of constraints plus one in the epigraph form (30) of (D), as in the Shapley–Folkman lemma; with Proposition 3.8 it yields $\psi(k)\le\phi(k+4)$.
--
--   **Formalization Note** (D) is the corrected dual (without the term $-(x^\top g)$). Optimality is stated as $D(x)\ge D(x')$ for every feasible $x'$.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 13, Proposition 3.9; proof pp. 13–14

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model
import Definitions.Def_NaiveFS_Multinomial_Dual

open Finset

namespace NaiveFS.Multinomial

/-- Proposition 3.9, p. 13: problem (D) (corrected) has an optimal solution with at most four
nonbinary pairs `(xᵢ, zᵢ)`, `z = 1 − x`. -/
theorem prop_3_9 {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hkm : k < m) :
    ∃ x : Fin m → ℝ, DFeasible k x ∧ (∀ x', DFeasible k x' → Dobj fp fm x' ≤ Dobj fp fm x) ∧
      (univ.filter (fun i => x i ≠ 0 ∧ x i ≠ 1)).card ≤ 4 := by sorry

end NaiveFS.Multinomial
