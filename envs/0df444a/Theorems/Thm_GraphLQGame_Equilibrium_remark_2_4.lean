-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_remark_2_4
-- name    : GraphLQGame.Equilibrium.remark_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:25:35.151918+00:00
-- url     : https://prove2.me/theorems/fbb4b1ac-69c9-4953-a18f-d1131d427c15
-- title:
--   Remark 2.4 — the eigenvalues of $L_G$ are real and lie in $[-2,0]$; $L_G\mathbf 1 = 0$
-- statement:
--   Let $G$ be a finite graph on $n$ vertices without isolated vertices. Then $L_G$ has only real eigenvalues, all of them in $[-2,0]$:
--   $$\lambda\in\mathrm{spec}(L_G)\ \Longrightarrow\ \lambda\in\mathbb R,\ -2\le\lambda\le0,$$
--   and the all-ones vector $\mathbf 1$ is an eigenvector with eigenvalue $0$: $L_G\mathbf 1=0$.
--
--   This places the eigenvalue distribution $\mu_G$ in the class of measures on $[-2,0]$ studied in §3.
--
--   **Formalization Note** "All eigenvalues are real" is stated as: the characteristic polynomial of $L_G$ has $n$ real roots counted with multiplicity; each of them lies in $[-2,0]$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Remark 2.4, p. 6

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, Remark 2.4, p. 6: for a graph without isolated vertices,
`L_G` has real eigenvalues, all between `−2` and `0`, and the all-ones vector is an
eigenvector with eigenvalue `0`.

Formalization Note: "all eigenvalues are real" is stated as: the characteristic polynomial of
`L_G` (degree `n`) has `n` real roots counted with multiplicity. -/
theorem remark_2_4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hN : NoIsolated G) :
    (lap G).charpoly.roots.card = n ∧
      (∀ l ∈ (lap G).charpoly.roots, -2 ≤ l ∧ l ≤ 0) ∧
      (lap G).mulVec (fun _ => (1 : ℝ)) = 0 := by sorry

end GraphLQGame.Equilibrium
