-- Prove2me | Theorems.Thm_MFGPlanning_Penalized_eq_13
-- name    : MFGPlanning.Penalized.eq_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:59:01.244983+00:00
-- url     : https://prove2.me/theorems/0136972a-3ff9-47b6-93c4-e1f1443692af
-- title:
--   (13) — coercivity of the numerical Hamiltonian in the discrete gradient
-- statement:
--   Assume the numerical Hamiltonian $g$ satisfies the coercivity hypothesis (G5). Then
--   $$
--   \lim_{\|[D_hU]\|_\infty \to \infty} \frac{\max_{i,j} g(x_{i,j}, [D_hU]_{i,j})}{\|[D_hU]\|_\infty} = +\infty,
--   $$
--   that is: for every $R$ there is $L$ such that every grid function $U$ with $\|[D_hU]\|_\infty \ge L$ has a grid point $(i,j)$ with $g(x_{i,j}, [D_hU]_{i,j}) \ge R\,\|[D_hU]\|_\infty$.
--
--   This is the form in which (G5) is used to bound the discrete value function: it makes the functional $J$ of (57) coercive in the proof of Proposition 3.
--
--   **Formalization Note** $\|[D_hU]\|_\infty$ is the maximum over all grid points and all four components of $[D_hU]_{i,j}$. Only (G5) is assumed, as on the page.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §2, eq. (13), p. 5

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp

namespace MFGPlanning.Penalized

/-- (13), hal-00465404v1, §2, p. 5 (PDF 6): the coercivity (G₅) implies
lim_{‖[D_hU]‖_∞ → ∞} max_{i,j} g(x_{i,j}, [D_hU]_{i,j}) / ‖[D_hU]‖_∞ = +∞.
Formalization Note: the limit is written as "for every R there is L such that
‖[D_hU]‖_∞ ≥ L implies max_{i,j} g(x_{i,j}, [D_hU]_{i,j}) ≥ R ‖[D_hU]‖_∞", and the maximum over
grid points as an existential. Only (G₅) is assumed, as on the page. -/
theorem eq_13 (d : Data) (hG5 : G5 d) :
    ∀ R : ℝ, ∃ L : ℝ, ∀ U : Pt d → ℝ, L ≤ supNormDh d U →
      ∃ p : Pt d, R * supNormDh d U ≤ d.g p (Dh d U p) := by sorry

end MFGPlanning.Penalized
