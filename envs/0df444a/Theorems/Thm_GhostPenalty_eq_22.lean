-- Prove2me | Theorems.Thm_GhostPenalty_eq_22
-- name    : GhostPenalty.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:02.428459+00:00
-- url     : https://prove2.me/theorems/905dc5b0-678f-49ea-908b-859afb0cc7ea
-- title:
--   (22) — $\nabla f(x)^Td(x)\le-c\|d(x)\|^2+\theta(x)\,\xi^Te$
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Let $d$ be the solution map of $(\mathrm P_x)$ on $K$. For every $x\in K$ and every KKT multiplier $\xi\in\Lambda(x)$ of $(\mathrm P_x)$ at $d(x)$,
--   $$\nabla f(x)^Td(x)\le-c\|d(x)\|^2+\theta(x)\,\xi^Te,\qquad \xi^Te=\sum_{i=1}^m\xi_i. \tag{22}$$
--   So $d(x)$ is a descent direction for $f$ up to a term proportional to the stationarity measure $\theta$.
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - encoding: d(x) = argmin of (Pₓ), the unique solution → a map d with hypothesis IsSubproblemSolutionMap (d(x) ∈ X̃(x) minimizes f̃(•;x) for every x ∈ K); reason: the minimizer exists and is unique under Assumption A (milestone subproblem_well_posed), so d is the source's map on K
--   - generalization: at the iterates x^ν with the multipliers ξ^ν of (18) → at every x ∈ K and every multiplier ξ ∈ Λ(x); reason: the derivation (18)–(21) uses only x^ν ∈ K and ξ^ν ∈ Λ(x^ν)
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Theorem 1, proof, (22), p.14

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_IsSubproblemSolutionMap
import Definitions.Def_GhostPenalty_KKTMult
import Definitions.Def_GhostPenalty_theta
open scoped RealInnerProductSpace

namespace GhostPenalty

/-- **Inequality (22): `d(x)` is nearly a descent direction for `f`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Theorem 1, proof, (22), p.14: "Therefore, recalling definition (14),
`∇f(x^ν)ᵀd(x^ν) ≤ −c‖d(x^ν)‖² + θ(x^ν)ξ^νᵀe`. (22)", where `ξ^ν` are KKT multipliers of
`(P_{x^ν})` at `d(x^ν)` (18) and `c` is the strong convexity modulus of A1.

For every `x ∈ K` and every KKT multiplier `ξ ∈ Λ(x)` of `(Pₓ)` at `d(x)`,
`⟨∇f(x), d(x)⟩ ≤ −c‖d(x)‖² + θ(x) ∑_i ξ_i`.

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. `d` solves (Pₓ) at every `x ∈ K`. The inequality is stated for a general `x ∈ K` and
multiplier, not only along a run; `ξᵀe = ∑_i ξ_i`, and `‖·‖` is the Euclidean norm. -/
theorem eq_22 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c)
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hd : IsSubproblemSolutionMap ft g gt K lam ρ β d) :
    ∀ x ∈ K, ∀ ξ ∈ KKTMult ft g gt K lam ρ β d x,
      ⟪gradient f x, d x⟫ ≤ -c * ‖d x‖ ^ 2 + theta g gt K lam ρ x * ∑ i, ξ i := by sorry

end GhostPenalty
