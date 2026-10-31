-- Prove2me | Theorems.Thm_GhostPenalty_proposition_2
-- name    : GhostPenalty.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:06.506877+00:00
-- url     : https://prove2.me/theorems/5c94a131-10b7-4da8-ae45-2f9186ab65ac
-- title:
--   Proposition 2 — $\kappa$ is continuous on $K$, and locally Lipschitz if $\tilde g$ is
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Then $\kappa$ is continuous on $K$ relative to $K$. If, in addition, $\tilde g(\cdot;\cdot)$ is locally Lipschitz continuous on $O_d\times O_x$, then $\kappa$ is also locally Lipschitz continuous on $K$.
--
--   **Formalization Note** "Locally Lipschitz on $K$" is Mathlib's `LocallyLipschitzOn K` (relative neighbourhoods; $\kappa$ is defined only on $K$); the extra hypothesis is imposed on each $\tilde g_i$.
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - reading: κ(•) locally Lipschitz continuous on K → LocallyLipschitzOn K κ, i.e. Lipschitz on a neighbourhood of each point of K relative to K; the hypothesis on g̃(•;•) is imposed on each g̃_i; reason: (8) defines κ only for x ∈ K, so K is the domain of the function and relative neighbourhoods are the only ones it has
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Proposition 2, p.10

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_kappa

namespace GhostPenalty

/-- **Proposition 2: continuity and local Lipschitz continuity of `κ`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Proposition 2, p.10: "Under Assumption A, `κ(•)` is continuous on `K` relative to `K`.
If, in addition, `g̃(•;•)` is locally Lipschitz continuous on `O_d × O_x`, then `κ(•)` is also
locally Lipschitz continuous on `K`."

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. "Locally Lipschitz continuous on `K`" is Mathlib's `LocallyLipschitzOn K`
(Lipschitz on a neighbourhood of each point of `K` relative to `K`; `κ` is defined only on `K`).
"`g̃(•;•)` locally Lipschitz on `O_d × O_x`" is required of each component `g̃_i`. -/
theorem proposition_2 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c) :
    ContinuousOn (kappa g gt K lam ρ) K ∧
      ((∀ i, LocallyLipschitzOn (Od ×ˢ Ox)
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => gt i p.1 p.2)) →
        LocallyLipschitzOn K (kappa g gt K lam ρ)) := by sorry

end GhostPenalty
