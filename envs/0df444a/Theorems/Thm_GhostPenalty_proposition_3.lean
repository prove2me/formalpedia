-- Prove2me | Theorems.Thm_GhostPenalty_proposition_3
-- name    : GhostPenalty.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:25.888728+00:00
-- url     : https://prove2.me/theorems/d6d89b85-a175-4a5f-966c-d3f702adda65
-- title:
--   Proposition 3 — $\theta\ge0$ is continuous, vanishes exactly at stationary points of (4), and $\theta(x)\le\|\nabla g(x)\|_\infty\|d(x)\|$
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Then:
--
--   1. $\theta(x)\ge 0$ for every $x\in K$, and $\theta$ is continuous on $K$ relative to $K$;
--   2. for $\hat x\in K$, $\theta(\hat x)=0$ if and only if $\hat x$ is a stationary point of the violation problem (4), i.e. satisfies (5);
--   3. if $d$ is the solution map of $(\mathrm P_x)$ on $K$, then for every $x\in K$
--   $$\theta(x)\le\|\nabla g(x)\|_\infty\,\|d(x)\|. \tag{15}$$
--
--   Here $\|\nabla g(x)\|_\infty=\max_i\|\nabla g_i(x)\|$ and $\|d(x)\|$ is Euclidean.
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - reading: ‖∇g(x)‖∞ in (15) → max_i ‖∇g_i(x)‖ (⨆ i, ‖gradient (g i) x‖); reason: the proof bounds ‖∇g(x)ᵀd‖∞ by ‖∇g(x)‖∞‖d‖, which requires the norm of ∇g(x)ᵀ from (ℝⁿ,‖·‖₂) to (ℝᵐ,‖·‖∞); that norm is max_i ‖∇g_i(x)‖, the smallest compatible constant, so the Lean bound implies (15) for any compatible reading
--   - encoding: stationary point of (4): 0 ∈ ∂max_i{g_i(x̂)+} + N_K(x̂) → IsViolationStationary: −v ∈ N_K(x̂) for some v in the convex hull of the active gradients (and 0 when the violation is 0); reason: that convex hull is the (Clarke = regular) subdifferential of a max of finitely many C¹ functions
--   - encoding: d(x) = argmin of (Pₓ), the unique solution → a map d with hypothesis IsSubproblemSolutionMap (d(x) ∈ X̃(x) minimizes f̃(•;x) for every x ∈ K); reason: the minimizer exists and is unique under Assumption A (milestone subproblem_well_posed), so d is the source's map on K
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Proposition 3, (15), p.11

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_theta
import Definitions.Def_GhostPenalty_IsViolationStationary
import Definitions.Def_GhostPenalty_IsSubproblemSolutionMap

namespace GhostPenalty

/-- **Proposition 3: `θ` is a continuous stationarity measure for the violation problem (4).**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Proposition 3, p.11: "Under Assumption A, (i) the nonnegative function `θ(•)` is
continuous on `K` relative to `K`; (ii) `θ(x̂) = 0` if and only if `x̂` is a stationary point
for problem (4); (iii) we have, for every `x ∈ K`, `θ(x) ≤ ‖∇g(x)‖∞‖d(x)‖`. (15)"

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. In (i), nonnegativity and continuity are on `K`. In (ii), `x̂` ranges over `K` and
stationarity for (4) is condition (5) (`IsViolationStationary`). In (iii), `d` is any map solving
(Pₓ) at every `x ∈ K`, and `‖∇g(x)‖∞` is read as `max_i ‖∇g_i(x)‖`, the norm of
`∇g(x)ᵀ : (ℝⁿ, ‖·‖₂) → (ℝᵐ, ‖·‖∞)` (the least constant with `‖∇g(x)ᵀd‖∞ ≤ C‖d‖`, the inequality the
proof uses); it is `0` when `m = 0`. -/
theorem proposition_3 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c) :
    ((∀ x ∈ K, 0 ≤ theta g gt K lam ρ x) ∧ ContinuousOn (theta g gt K lam ρ) K) ∧
      (∀ xh ∈ K, theta g gt K lam ρ xh = 0 ↔ IsViolationStationary g K xh) ∧
      (∀ d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        IsSubproblemSolutionMap ft g gt K lam ρ β d →
        ∀ x ∈ K, theta g gt K lam ρ x ≤ (⨆ i, ‖gradient (g i) x‖) * ‖d x‖) := by sorry

end GhostPenalty
