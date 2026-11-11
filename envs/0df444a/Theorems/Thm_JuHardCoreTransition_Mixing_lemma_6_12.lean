-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_6_12
-- name    : JuHardCoreTransition.Mixing.lemma_6_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:28.424495+00:00
-- url     : https://prove2.me/theorems/f9d0f491-a8e9-40c1-b42b-aed9aa7839e7
-- title:
--   Lemma 6.12 — elementary bounds for Glauber dynamics and padding
-- statement:
--   Let $G$ be a graph on $n\ge2$ vertices and $\lambda>0$. The Glauber dynamics for $\mu_{G,\lambda}$ satisfies
--   $$t_{\mathrm{rel}}\ge n,\qquad t_{\mathrm{mix}}(1/4)\ge(t_{\mathrm{rel}}-1)\log2\ge(n-1)\log2 .$$
--   If $G$ is the disjoint union of a graph $G_0$ on $n_0\ge1$ vertices and another graph, then at the same fugacity $t_{\mathrm{rel}}(G)\ge\frac n{n_0}t_{\mathrm{rel}}(G_0)$.
--
--   Differences from the source:
--   - encoding: G is the disjoint union of G₀ and another graph → G = G₀ ⊕g G₁ on V₀ ⊕ V₁, with n = |V₀ ⊕ V₁| ≥ 2; reason: disjoint union of simple graphs; the lemma's standing n ≥ 2 is kept
--   - encoding: the chain t_mix(1/4) ≥ (t_rel − 1) log 2 ≥ (n − 1) log 2 → two conjuncts; reason: same content
--   - encoding: t_rel = 1/(1−θ₂), t_mix from the worst initial state → trelG = 1/gap and tmixG = tmix of the published heat-bath kernel hcP at constant activity; reason: the published gap counts eigenvalue 1 with multiplicity; the chain is irreducible, so 1 − gap is θ₂
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 6.12, printed p.49 / PDF p.50

import Mathlib
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

/-- **Lemma 6.12 (Elementary bounds for Glauber dynamics)** (printed p.49 / PDF p.50). Let `G`
be a graph on `n ≥ 2` vertices and `λ > 0`. The Glauber dynamics for `μ_{G,λ}` satisfies
`t_rel ≥ n` and `t_mix(1/4) ≥ (t_rel − 1) log 2 ≥ (n − 1) log 2`. If `G` is the disjoint union of a
graph `G₀` on `n₀ ≥ 1` vertices and another graph `G₁`, then at the same fugacity
`t_rel(G) ≥ (n/n₀) t_rel(G₀)`. -/
theorem lemma_6_12 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {V₀ V₁ : Type*} [Fintype V₀] [DecidableEq V₀] [Fintype V₁]
    [DecidableEq V₁] (G₀ : SimpleGraph V₀) [DecidableRel G₀.Adj] (G₁ : SimpleGraph V₁)
    [DecidableRel G₁.Adj] [DecidableRel (G₀ ⊕g G₁).Adj] (lam : ℝ) (hlam : 0 < lam) :
    (2 ≤ Fintype.card V →
      (Fintype.card V : ℝ) ≤ trelG G lam ∧
      (trelG G lam - 1) * Real.log 2 ≤ (tmixG G lam (1 / 4) : ℝ) ∧
      ((Fintype.card V : ℝ) - 1) * Real.log 2 ≤ (trelG G lam - 1) * Real.log 2) ∧
    (1 ≤ Fintype.card V₀ → 2 ≤ Fintype.card (V₀ ⊕ V₁) →
      (Fintype.card (V₀ ⊕ V₁) : ℝ) / (Fintype.card V₀ : ℝ) * trelG G₀ lam ≤
        trelG (G₀ ⊕g G₁) lam) := by sorry

end JuHardCoreTransition.Mixing
