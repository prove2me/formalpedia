-- Prove2me | Theorems.Thm_MPBSelect_theorem_3_G_concave
-- name    : MPBSelect.theorem_3_G_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:28:28.698759+00:00
-- url     : https://prove2.me/theorems/1456e78a-b125-40d7-9bd5-f47a3e69d413
-- title:
--   Proof of Theorem 3, p.ec8 — each $G_i(\theta_b)$ and the objective of (20) are concave in $\boldsymbol\alpha$
-- statement:
--   Consider an MPB problem (with $k\ge2$, $p_b>0$, $\sum_bp_b=1$, assumptions (i)–(ii) and $\lambda>0$), and let $\mathbb R^{k\times B}_{\ge0}$ be the set of allocations $\boldsymbol\alpha$ with all entries nonnegative (boundary included). Then:
--
--   1. for every pair $(i,\theta_b)$ with $i\ne i^b$, the pairwise rate $\boldsymbol\alpha\mapsto G_i(\theta_b)$ is concave on $\mathbb R^{k\times B}_{\ge0}$;
--   2. the objective
--   $$
--   \boldsymbol\alpha\mapsto\min_{(i,\theta_b)\in\Xi}W_i(\theta_b)G_i(\theta_b)
--   $$
--   of (20) is concave on $\mathbb R^{k\times B}_{\ge0}$, which contains the feasible set of (20).
--
--   Clause 2 is what makes the epigraph form (EC.14) of (20) a convex program, so that the KKT conditions characterize its optima.
--
--   Differences from the source:
--   - reading: "each Gi(θb) is concave; thus, (EC.14) is a convex program" → concavity of each $G_i(\theta_b)$ ($i\ne i^b$) and of the objective of (20) on the closed nonnegative orthant; reason: the page names no domain, the orthant is where $G$ is defined by its two branches and it contains the feasible set; concavity of the objective on it is exactly convexity of (EC.14).
--   - reading: standing hypotheses $k\ge2$, $p_b>0$, $\lambda_i(\theta_b)>0$ (standard deviation) → fields of the problem; reason: for $k=1$ the objective is a minimum over the empty set, $\Theta$ is the support of $\pi$, and every formula divides by $p_b$ and $\lambda^2$.
--   - encoding: solutions, parameters and $\alpha$ → `Fin k`, `Fin B`, `Fin k → Fin B → ℝ`, with $i^b$, $i^*$ as fields characterized by their defining properties, and the minimum as `Finset.inf'`; reason: Lean convention; same instances.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, proof of Theorem 3, after (EC.14), p.ec8

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_G
import Definitions.Def_MPBSelect_Problem_ldr

namespace MPBSelect

/-- **Concavity of the pairwise rate and of the objective of (20).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
after (EC.14), p.ec8: "Note that harmonic mean function f(x,y) = 1/(1/x + 1/y) is concave in
both x and y, so each Gi(θb) is concave; thus, (EC.14) is a convex program."

1. For every pair `(i, θ_b)` with `i ≠ i^b`, the map `α ↦ G_i(θ_b)` is concave on the closed
   nonnegative orthant `{α | α_j(θ_c) ≥ 0 for all j, c}`, boundary included (where `G` takes its
   `otherwise 0` branch).
2. The objective `α ↦ LDR(α) = min_{(i,θ_b) ∈ Ξ} W_i(θ_b) G_i(θ_b)` of (20) is concave on the same
   orthant, which contains the feasible set of (20); this is what makes (EC.14) a convex program.

**Formalization Note** `α : Fin k → Fin B → ℝ` with the pointwise vector-space structure. -/
theorem theorem_3_G_concave {k B : ℕ} (P : Problem k B) :
    (∀ (i : Fin k) (b : Fin B), i ≠ P.ib b →
      ConcaveOn ℝ {α : Fin k → Fin B → ℝ | ∀ j c, 0 ≤ α j c} (fun α => P.G α i b)) ∧
    ConcaveOn ℝ {α : Fin k → Fin B → ℝ | ∀ j c, 0 ≤ α j c} P.ldr := by sorry

end MPBSelect
