-- Prove2me | Theorems.Thm_GhostPenalty_subproblem_well_posed
-- name    : GhostPenalty.subproblem_well_posed
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:43.757064+00:00
-- url     : https://prove2.me/theorems/10f835a1-3d96-41dc-b410-788a0533cf44
-- title:
--   Well-posedness of $(\mathrm P_x)$: $\widetilde X(x)\neq\emptyset$ and a unique minimizer
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Then for every $x\in K$ the feasible set $\widetilde X(x)$ of the subproblem $(\mathrm P_x)$ is nonempty and $\tilde f(\cdot;x)$ has exactly one minimizer over $\widetilde X(x)$:
--   $$\widetilde X(x)\neq\emptyset\quad\text{and}\quad \exists!\,u\in\widetilde X(x):\ \tilde f(u;x)\le\tilde f(v;x)\ \ \forall v\in\widetilde X(x).$$
--   This is what makes the direction $d(x)$ of Algorithm 1 well defined ("The algorithm is always well defined if Assumption A, which guarantees existence and uniqueness of $d(x^\nu)$, holds").
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §3.2, p.9 and §4, p.13 (well-definedness of Algorithm 1)

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_Xt

namespace GhostPenalty

/-- **Well-posedness of the subproblem (Pₓ).**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3.2, p.9: "the feasible set of problem (Pₓ), for every `x ∈ K`, is nonempty", and
§4, p.13: "The algorithm is always well defined if Assumption A, which guarantees existence and
uniqueness of `d(x^ν)`, holds."

Under Assumption A, for every `x ∈ K` the feasible set `X̃(x)` is nonempty and `f̃(·;x)` has
exactly one minimizer over `X̃(x)`.

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. -/
theorem subproblem_well_posed {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c) :
    ∀ x ∈ K, (Xt g gt K lam ρ β x).Nonempty ∧
      ∃! u, u ∈ Xt g gt K lam ρ β x ∧ ∀ v ∈ Xt g gt K lam ρ β x, ft u x ≤ ft v x := by sorry

end GhostPenalty
