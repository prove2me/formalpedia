-- Prove2me | Theorems.Thm_HardCoreBochner_hardcore_M
-- name    : HardCoreBochner.hardcore_M
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:05.90457+00:00
-- url     : https://prove2.me/theorems/7e7c884c-60c1-42ab-bf00-470d3bbe9262
-- title:
--   Proof of Theorem 1.1 — $M_\sigma=\lambda(I(1-\delta)+\lambda(I+A_{G_\sigma}))$ for the hard-core model
-- statement:
--   Let $G$ be a finite graph, $\lambda>0$, $\delta\in\mathbb R$, and $\mu=\mu_{G,\lambda}$ the hard-core model. Write $V(G_\sigma)$ for the vertices of $G_\sigma$, the graph left after removing an independent set $\sigma$ and its neighbours. Then:
--
--   1. $\mu$ is a distribution whose support $X$ is exactly the set of independent sets of $G$, and $X$ is downward-closed;
--   2. for every independent set $\sigma$ and $v\in V$: $r_v(\sigma)=\lambda$ if $v\in V(G_\sigma)$ and $r_v(\sigma)=0$ otherwise;
--   3. for every independent set $\sigma$ and $u,v\in V$:
--   $$M_\sigma(u,v)=\begin{cases}\lambda\big((1-\delta+\lambda)\mathbf 1_{u=v}+\lambda A_G(u,v)\big)&\text{if } u,v\in V(G_\sigma),\\ 0&\text{otherwise,}\end{cases}$$
--   that is, $M_\sigma=\lambda\big(I(1-\delta)+\lambda(I+A_{G_\sigma})\big)$ on $V(G_\sigma)$ and zero elsewhere.
--
--   Together with interlacing this reduces hypothesis (3) of Theorem 1.2 for the hard-core model to $\lambda\le(1-\delta)/(-\lambda_{\min}(A_G)-1)$.
--
--   Differences from the source:
--   - generalization: M_σ = λ(I(1 − δ) + λ(I + A_{G_σ})), with 'Here X is the set of independent sets of G' and r_v(σ) used implicitly → also concludes IsDownClosedLaw µ_{G,λ}, supp µ_{G,λ} = independent sets, and r_v(σ) = λ·1{v ∈ V(G_σ)}; reason: the extra clauses are the facts the page relies on, now stated as conclusions; the M_σ clause is the printed one
--   - generalization: δ ∈ (0, 1) → δ any real; reason: the identity is algebraic in δ; δ ∈ (0, 1) is a special case
--   - reading: M_σ ∈ ℝ^{V×V} equated with the V(G_σ) × V(G_σ) matrix λ(I(1 − δ) + λ(I + A_{G_σ})) → the printed entries on V(G_σ) × V(G_σ) and 0 elsewhere; reason: r_v(σ) = 0 for v ∉ V(G_σ) kills those columns, and the rows u ∉ V(G_σ) vanish; this is the only consistent reading of the dimensions
--   - encoding: µ_{G,λ} and A_G → MarkovMixing.hardcoreDist G λ and G.adjMatrix ℝ; reason: published hard-core law and Mathlib adjacency matrix; same objects
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), proof of Theorem 1.1, p.4 (PDF p.4)

import Definitions.Def_mm_coupling
import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_Mmat
import Definitions.Def_HardCoreBochner_avail

namespace HardCoreBochner

open scoped BigOperators

/-- **The local matrix of the hard-core model.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof of Theorem 1.1, p.4: "Here X is the set
of independent sets of G. [...] We note that Mσ = λ (I(1 − δ) + λ(I + AGσ)) where AGσ is the adjacency
matrix of Gσ."

For `λ > 0`:
1. `µ_{G,λ}` is a distribution whose support is exactly the independent sets, and that support is
   downward-closed;
2. at an independent set `σ`, `r_v(σ) = λ` if `v` is a vertex of `G_σ` and `0` otherwise;
3. at an independent set `σ`, for all `u, v ∈ V`:
   `M_σ(u, v) = λ((1 − δ + λ) 1_{u=v} + λ A_G(u, v))` if `u, v` are both vertices of `G_σ`, and `0`
   otherwise.

**Formalization Note** `M_σ` is `V × V`, while the printed right-hand side is a `V(G_σ) × V(G_σ)`
matrix; (3) reads it with zero rows and columns outside `V(G_σ)`, where the vertices of `G_σ` are
`avail G σ` and `A_{G_σ}` is the restriction of `A_G`. `µ_{G,λ}` is the published
`MarkovMixing.hardcoreDist`. -/
theorem hardcore_M {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (lam : ℝ) (hlam : 0 < lam) (δ : ℝ) :
    IsDownClosedLaw (MarkovMixing.hardcoreDist G lam) ∧
      (∀ σ, 0 < MarkovMixing.hardcoreDist G lam σ ↔ MarkovMixing.IsHardcore G σ) ∧
      (∀ σ, MarkovMixing.IsHardcore G σ → ∀ v,
        rate (MarkovMixing.hardcoreDist G lam) v σ = if avail G σ v then lam else 0) ∧
      (∀ σ, MarkovMixing.IsHardcore G σ → ∀ u v,
        Mmat (MarkovMixing.hardcoreDist G lam) δ σ u v =
          if avail G σ u ∧ avail G σ v then
            lam * ((1 - δ + lam) * (if u = v then 1 else 0) + lam * G.adjMatrix ℝ u v)
          else 0) := by sorry

end HardCoreBochner
