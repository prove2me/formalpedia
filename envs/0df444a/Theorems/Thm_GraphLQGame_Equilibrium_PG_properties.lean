-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_PG_properties
-- name    : GraphLQGame.Equilibrium.PG_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:26:50.932473+00:00
-- url     : https://prove2.me/theorems/b5d1a94a-1c0c-4663-bb99-57d1779bbf95
-- title:
--   §4.4, p. 26, properties (i)–(iii) — $e_i^\top P(t)e_i = \mathrm{Tr}(P(t))/n > 0$, $P(t)$ symmetric PSD with the kernel dimension of $L$, $PL = LP$
-- statement:
--   Let $G$ be a finite transitive graph on $n\ge1$ vertices without isolated vertices, $c,T>0$, $f$ the solution of $f'=cQ_G'(f)$, $f(0)=0$ on $[0,T]$, and $P(t)=P_G(t)$ as in (2.5). For each $t\in[0,T]$:
--
--   1. $e_i^\top P(t)e_i=\frac1n\mathrm{Tr}(P(t))>0$ for all $i$;
--   2. $P(t)$ is symmetric and positive semidefinite, and $L$ and $P(t)$ both have $0$ as an eigenvalue, with the same multiplicity;
--   3. $P(t)L=LP(t)$.
--
--   Property 1 is what makes the candidate $F^i$ of (4.13) well defined.
--
--   **Formalization Note** The multiplicity of $0$ is the dimension of the kernel (both matrices are symmetric). $n\ge1$ is added: on the empty graph $0$ is not an eigenvalue. $f'(T-t)$ in $P_G$ is $cQ_G'(f(T-t))$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §4.4, p. 26, properties (i)–(iii)

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, §4.4, p. 26, properties (i)–(iii). Let `G` be a finite
transitive graph on `n ≥ 1` vertices without isolated vertices, `c, T > 0`, `f` the solution of
`f' = c Q_G'(f)`, `f(0) = 0` on `[0, T]`, and `P(t) = P_G(t)` as in (2.5). For each `t ∈ [0, T]`:
(i) `e_iᵀ P(t) e_i = Tr(P(t))/n > 0` for all `i`;
(ii) `P(t)` is symmetric and positive semidefinite; both `L` and `P(t)` have `0` as an eigenvalue,
with the same multiplicity;
(iii) `P(t)` and `L` commute.

Formalization Note: vertices are `Fin n`; the multiplicity of the eigenvalue `0` is the dimension
of the kernel (both matrices are symmetric). `0 < n` is added: for the empty graph `0` is not an
eigenvalue. `f'(T − t)` inside `P_G` is written `c Q_G'(f(T − t))`. -/
theorem PG_properties {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 0 < n)
    (hT : IsTransitive G) (hN : NoIsolated G) (c T : ℝ) (hc : 0 < c) (hTpos : 0 < T)
    (f : ℝ → ℝ) (hf : IsFSol c T (QG G) f) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∀ i : Fin n, PG G c T f t i i = (n : ℝ)⁻¹ * (PG G c T f t).trace ∧
        0 < (n : ℝ)⁻¹ * (PG G c T f t).trace) ∧
      ((PG G c T f t).transpose = PG G c T f t ∧ (PG G c T f t).PosSemidef ∧
        Module.End.HasEigenvalue (Matrix.toLin' (lap G)) 0 ∧
        Module.End.HasEigenvalue (Matrix.toLin' (PG G c T f t)) 0 ∧
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (PG G c T f t))) =
          Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (lap G)))) ∧
      PG G c T f t * lap G = lap G * PG G c T f t := by sorry

end GraphLQGame.Equilibrium
