-- Prove2me | Theorems.Thm_HardCoreBochner_lemma_2_2
-- name    : HardCoreBochner.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:11.812296+00:00
-- url     : https://prove2.me/theorems/a0b2137b-e59a-429f-9972-6855cb55a72e
-- title:
--   Lemma 2.2 — commutator identity $D^+_vL=L^{(v)}D^+_v-D^+_v+\sum_u(D^+_vr_u)D^+_u$
-- statement:
--   Let $\mu$ be a distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$. Fix $v\in V$. For every $\sigma\in X$ with $v\notin\sigma$ and every $f:\{0,1\}^V\to\mathbb R$,
--   $$D^+_vLf(\sigma)=L^{(v)}(D^+_vf)(\sigma)-D^+_vf(\sigma)+\sum_{u\in V}(D^+_vr_u)(\sigma)\,D^+_uf(\sigma),\tag{11}$$
--   where $(D^+_vr_u)(\sigma)=r_u(\sigma\cup\{v\})-r_u(\sigma)$ and $L^{(v)}$ is the generator of the pinned family.
--
--   The identity says that differentiating in the direction $v$ commutes with the dynamics up to the pinned generator and an interaction term measuring how adding $v$ changes the other birth rates.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), Lemma 2.2, (11), p.8 (PDF p.8)

import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_pinGen

namespace HardCoreBochner

open scoped BigOperators

/-- **Lemma 2.2** (commutator identity). Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), Lemma 2.2, (11), p.8.

Fix `v ∈ V`. For every `σ ∈ X` with `v ∉ σ`,
`D⁺_v Lf(σ) = L^(v)(D⁺_v f)(σ) − D⁺_v f(σ) + Σ_{u∈V} (D⁺_v r_u)(σ) D⁺_u f(σ)`,
where `(D⁺_v r_u)(σ) = r_u(σ ∪ {v}) − r_u(σ)`.

**Formalization Note** `σ ∈ X` is `0 < µ σ`, `v ∉ σ` is `σ v = false`; `L^(v)` is `pinGen µ v`, the
printed formula. -/
theorem lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (hμ : IsDownClosedLaw μ) (v : V) (f : (V → Bool) → ℝ) (σ : V → Bool) (hσ : 0 < μ σ)
    (hv : σ v = false) :
    Dplus v (gen μ f) σ =
      pinGen μ v (Dplus v f) σ - Dplus v f σ +
        ∑ u, (rate μ u (Function.update σ v true) - rate μ u σ) * Dplus u f σ := by sorry

end HardCoreBochner
