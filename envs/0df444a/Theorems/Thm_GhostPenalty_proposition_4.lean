-- Prove2me | Theorems.Thm_GhostPenalty_proposition_4
-- name    : GhostPenalty.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:01.277875+00:00
-- url     : https://prove2.me/theorems/0ff7a5f8-4da3-4155-afdc-34885703c533
-- title:
--   Proposition 4 — under the eMFCQ, MFCQ holds on $\widetilde X(\hat x)$ and $d(\cdot)$ is continuous near $\hat x$
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Let the eMFCQ hold at $\hat x\in K$. Then:
--
--   1. the MFCQ holds at every point $u\in\widetilde X(\hat x)$ for the subproblem $(\mathrm P_{\hat x})$: the only $\xi\in\mathbb R^m$ with $\xi\ge 0$, $\xi_i(\tilde g_i(u;\hat x)-\kappa(\hat x))=0$ for all $i$, and $-\sum_i\xi_i\nabla_1\tilde g_i(u;\hat x)\in N_{\beta\mathbb B^n_\infty\cap(K-\hat x)}(u)$, is $\xi=0$;
--   2. if $d$ is the solution map of $(\mathrm P_x)$ on $K$, there is a neighbourhood $V$ of $\hat x$ such that $d$ is continuous relative to $K$ at every $x\in K\cap V$.
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - reading: the MFCQ holds at u for subproblem (P_x̂) → multiplier form: no nonzero ξ ≥ 0, complementary to the active surrogate constraints, with −∑ξ_i∇₁g̃_i(u;x̂) ∈ N_{βBⁿ∞∩(K−x̂)}(u); reason: the problem has an abstract convex set constraint, for which the MFCQ is stated in this dual form; it is the form of the paper's own eMFCQ (Definition 2)
--   - encoding: d(x) = argmin of (Pₓ), the unique solution → a map d with hypothesis IsSubproblemSolutionMap (d(x) ∈ X̃(x) minimizes f̃(•;x) for every x ∈ K); reason: the minimizer exists and is unique under Assumption A (milestone subproblem_well_posed), so d is the source's map on K
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Proposition 4, p.11

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_Xt
import Definitions.Def_GhostPenalty_EMFCQ
import Definitions.Def_GhostPenalty_IsSubproblemSolutionMap
open FirstOrderOpt.ConvexTheory
open Filter Topology

namespace GhostPenalty

/-- **Proposition 4: MFCQ for the subproblem and continuity of `d(·)` under the eMFCQ.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Proposition 4, p.11: "Under Assumption A, let the eMFCQ hold at `x̂ ∈ K` for problem
(P). Then, (i) the MFCQ holds at every point of `X̃(x̂)` for subproblem `(P_x̂)`; (ii) a
neighborhood `V` of `x̂` exists such that, for every point `x ∈ K ∩ V`, the function `d(•)` is
continuous relative to `K`."

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. The MFCQ for `(P_x̂)` (constraints `g̃(·;x̂) ≤ κ(x̂)e` and the convex set
`βBⁿ∞ ∩ (K − x̂)`) at `u ∈ X̃(x̂)` is written in multiplier form, like the eMFCQ of Definition 2:
the only `ξ ≥ 0` with `ξ_i (g̃_i(u;x̂) − κ(x̂)) = 0` and `−∑_i ξ_i ∇₁g̃_i(u;x̂) ∈ N_{βBⁿ∞∩(K−x̂)}(u)`
is `ξ = 0`. In (ii), `d` is any map solving (Pₓ) at every `x ∈ K`; continuity relative to `K`
is `ContinuousWithinAt d K x`. `EMFCQ g K xh` contains `x̂ ∈ K`. -/
theorem proposition_4 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c) (xh : EuclideanSpace ℝ (Fin n)) (hcq : EMFCQ g K xh) :
    (∀ u ∈ Xt g gt K lam ρ β xh, ∀ ξ : Fin m → ℝ, (∀ i, 0 ≤ ξ i) →
        (∀ i, ξ i * (gt i u xh - kappa g gt K lam ρ xh) = 0) →
        -(∑ i, ξ i • gradient (fun v => gt i v xh) u) ∈
          normalCone (box n β ∩ {v | xh + v ∈ K}) u →
        ξ = 0) ∧
      (∀ d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        IsSubproblemSolutionMap ft g gt K lam ρ β d →
        ∃ V ∈ 𝓝 xh, ∀ x ∈ K ∩ V, ContinuousWithinAt d K x) := by sorry

end GhostPenalty
