-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_Fmat_solves_riccati
-- name    : GraphLQGame.Equilibrium.Fmat_solves_riccati
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:28:13.066977+00:00
-- url     : https://prove2.me/theorems/d81c76fd-9c23-4136-a8aa-96de88004215
-- title:
--   §4.4, pp. 26–28 — the matrices $F^i$ of (4.13) satisfy $e_i^\top F^i = e_i^\top P$ and solve (4.6) with $F^i(T) = cLe_ie_i^\top L$
-- statement:
--   Let $G$ be a finite transitive graph without isolated vertices, $c,T>0$, $f$ the solution of $f'=cQ_G'(f)$, $f(0)=0$ on $[0,T]$, $P=P_G$, and
--   $$F^i(t)=\frac{1}{\mathrm{Tr}(P(t))/n}\,P(t)e_ie_i^\top P(t).\qquad(4.13)$$
--   Then $e_i^\top F^i(t)=e_i^\top P(t)$ for $t\in[0,T]$; each $F^i$ is differentiable on $(0,T)$ and $(F^1,\dots,F^n)$ solves the Riccati system (4.6) there; and $F^i(T)=cLe_ie_i^\top L$.
--
--   Together with Lemma 4.2 this exhibits the explicit solution of the Nash system whose feedback is $\alpha^G_i(t,x)=-e_i^\top P(t)x$.
--
--   **Formalization Note** $e_i^\top F^i=e_i^\top P$ is equality of the $i$-th rows. $f'(T-t)$ in $P_G$ is $cQ_G'(f(T-t))$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §4.4, pp. 26–28, (4.13), display after (4.13), and the conclusion on p. 28

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Equilibrium_NashSystem

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, §4.4, pp. 26–28: with `P = P_G` from (2.5) and
`Fⁱ(t) = (Tr(P(t))/n)⁻¹ P(t) e_i e_iᵀ P(t)` (4.13),
`e_iᵀ Fⁱ(t) = e_iᵀ P(t)` for `t ∈ [0, T]` (display after (4.13)), and `(F¹, …, Fⁿ)` solves (4.6)
on `(0, T)` with the boundary condition `Fⁱ(T) = c L e_i e_iᵀ L` of (4.7).

Formalization Note: vertices are `Fin n`; `e_iᵀ Fⁱ = e_iᵀ P` is the equality of the `i`-th rows;
differentiability of each entry of `Fⁱ` on `(0, T)` is asserted together with (4.6), whose time
derivative is entrywise. `f'(T − t)` inside `P_G` is written `c Q_G'(f(T − t))`. -/
theorem Fmat_solves_riccati {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) (hN : NoIsolated G) (c T : ℝ) (hc : 0 < c) (hTpos : 0 < T)
    (f : ℝ → ℝ) (hf : IsFSol c T (QG G) f) :
    (∀ i : Fin n, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : Fin n,
        Fmat G c T f i t i k = PG G c T f t i k) ∧
      (∀ i : Fin n, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        (∀ j k : Fin n, DifferentiableAt ℝ (fun s => Fmat G c T f i s j k) t) ∧
          riccatiRes (Fmat G c T f) i t = 0) ∧
      (∀ i : Fin n, Fmat G c T f i T = c • (lap G * Matrix.single i i 1 * lap G)) := by sorry

end GraphLQGame.Equilibrium
