-- Prove2me | Theorems.Thm_GhostPenalty_subproblem_solution_is_kkt
-- name    : GhostPenalty.subproblem_solution_is_kkt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:21.108271+00:00
-- url     : https://prove2.me/theorems/1aab3b2e-8f3b-45a4-8c41-7b4872b17ecc
-- title:
--   Proof of Theorem 1, p.14 — at a non-stationary $x\in K$, $d(x)$ is a KKT point of $(\mathrm P_x)$
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Let $d$ be the solution map of $(\mathrm P_x)$ on $K$. If $x\in K$ is not a generalized stationary solution of (P), then $d(x)$ is a KKT point of $(\mathrm P_x)$:
--   $$\Lambda(x)\neq\emptyset.$$
--   In the proof of Theorem 1 this is applied to every iterate $x^\nu$ of Algorithm 1, which is not generalized stationary because the method did not stop at (S.1): "at each step, the solution $d(x^\nu)$ of subproblem $(\mathrm P_{x^\nu})$ is also a KKT point for $(\mathrm P_{x^\nu})$".
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - encoding: d(x) = argmin of (Pₓ), the unique solution → a map d with hypothesis IsSubproblemSolutionMap (d(x) ∈ X̃(x) minimizes f̃(•;x) for every x ∈ K); reason: the minimizer exists and is unique under Assumption A (milestone subproblem_well_posed), so d is the source's map on K
--   - generalization: at each step of Algorithm 1 (an iterate x^ν at which (S.1) did not stop) → every x ∈ K that is not generalized stationary; reason: the proof uses only x^ν ∈ K and non-stationarity; every iterate is such a point
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Theorem 1, proof, p.14

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_IsSubproblemSolutionMap
import Definitions.Def_GhostPenalty_KKTMult
import Definitions.Def_GhostPenalty_IsGenStationary

namespace GhostPenalty

/-- **Proof of Theorem 1, p.14: away from generalized stationary points, `d(x)` is a KKT point
of `(Pₓ)`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Theorem 1, proof, p.14: "Preliminarily, observe that, at each step, the solution
`d(x^ν)` of subproblem `(P_{x^ν})` is also a KKT point for `(P_{x^ν})`."  The argument uses only
that the iterate `x^ν ∈ K` is not generalized stationary (otherwise the algorithm stops at
(S.1)).

For every `x ∈ K` that is not a generalized stationary solution of (P), the set `Λ(x)` of KKT
multipliers of `(Pₓ)` at `d(x)` is nonempty.

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. `d` solves (Pₓ) at every `x ∈ K`. The statement is made for every non-stationary
`x ∈ K` rather than along a run; every iterate of a run of Algorithm 1 is such a point. -/
theorem subproblem_solution_is_kkt {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c)
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hd : IsSubproblemSolutionMap ft g gt K lam ρ β d) :
    ∀ x ∈ K, ¬ IsGenStationary f g K x → (KKTMult ft g gt K lam ρ β d x).Nonempty := by sorry

end GhostPenalty
