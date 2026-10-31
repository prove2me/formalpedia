-- Prove2me | Theorems.Thm_GhostPenalty_proposition_6
-- name    : GhostPenalty.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:33.989996+00:00
-- url     : https://prove2.me/theorems/46047fca-6911-4027-9397-28bb4cb38172
-- title:
--   Proposition 6 — under Slater's CQ, $d(x)$ is a KKT point near $\hat x$ with locally bounded multipliers
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Let $d$ be the solution map of $(\mathrm P_x)$ on $K$, let $\hat x\in K$, and suppose there is $\hat d\in\beta\mathbb B^n_\infty\cap(K-\hat x)$ with $\tilde g(\hat d;\hat x)<\kappa(\hat x)e$. Then there is a neighbourhood $V$ of $\hat x$ such that for every $x\in K\cap V$ the solution $d(x)$ of $(\mathrm P_x)$ is a KKT point of $(\mathrm P_x)$, i.e. $\Lambda(x)\neq\emptyset$; and the multiplier map $\Lambda$ is locally bounded at $\hat x$ relative to $K$: there are a neighbourhood $U$ of $\hat x$ and $M$ with
--   $$\|\xi\|\le M\qquad\text{for all } x\in K\cap U,\ \xi\in\Lambda(x).$$
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - encoding: d(x) = argmin of (Pₓ), the unique solution → a map d with hypothesis IsSubproblemSolutionMap (d(x) ∈ X̃(x) minimizes f̃(•;x) for every x ∈ K); reason: the minimizer exists and is unique under Assumption A (milestone subproblem_well_posed), so d is the source's map on K
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Proposition 6, p.13

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_IsSubproblemSolutionMap
import Definitions.Def_GhostPenalty_KKTMult
open Filter Topology

namespace GhostPenalty

/-- **Proposition 6: KKT multipliers of (Pₓ) exist and are locally bounded under Slater's CQ.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Proposition 6, p.13: "Under Assumption A, let `x̂` belong to `K` and suppose that
`d̂ ∈ βBⁿ∞ ∩ (K − x̂)` exists such that `g̃(d̂; x̂) < κ(x̂)e`. Then, a neighborhood `V` of `x̂`
exists such that, for every point `x ∈ K ∩ V`, the unique solution `d(x)` of `(Pₓ)` is a KKT
point for problem `(Pₓ)` and the set-valued mapping of the KKT multipliers is locally bounded at
`x̂` relative to `K`."

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. `d` solves (Pₓ) at every `x ∈ K`; `KKTMult … d x` is the set `Λ(x)` of KKT multipliers
of (Pₓ) at `d(x)` (pp.12–13), and "`d(x)` is a KKT point" is `Λ(x) ≠ ∅`. Local boundedness at
`x̂` relative to `K`: there are a neighbourhood `U` of `x̂` and `M` with `‖ξ‖ ≤ M` for every
`ξ ∈ Λ(x)`, `x ∈ K ∩ U` (`‖·‖` the sup norm on `ℝᵐ`; boundedness does not depend on the norm). -/
theorem proposition_6 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c)
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hd : IsSubproblemSolutionMap ft g gt K lam ρ β d)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : xh ∈ K)
    (hslater : ∃ dh ∈ box n β ∩ {u | xh + u ∈ K}, ∀ i, gt i dh xh < kappa g gt K lam ρ xh) :
    ∃ V ∈ 𝓝 xh, (∀ x ∈ K ∩ V, (KKTMult ft g gt K lam ρ β d x).Nonempty) ∧
      ∃ U ∈ 𝓝 xh, ∃ M : ℝ, ∀ x ∈ K ∩ U, ∀ ξ ∈ KKTMult ft g gt K lam ρ β d x, ‖ξ‖ ≤ M := by sorry

end GhostPenalty
