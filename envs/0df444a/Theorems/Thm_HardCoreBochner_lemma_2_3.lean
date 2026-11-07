-- Prove2me | Theorems.Thm_HardCoreBochner_lemma_2_3
-- name    : HardCoreBochner.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:20.503523+00:00
-- url     : https://prove2.me/theorems/4f7558b7-8a67-4c84-869a-d8a7688705a6
-- title:
--   Lemma 2.3 — Bochner-type inequality for $\langle Lf,Lf\rangle_\mu$
-- statement:
--   Let $\mu$ be a distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$. For every $f:\{0,1\}^V\to\mathbb R$,
--   $$\langle Lf,Lf\rangle_\mu\ \ge\ -\langle f,Lf\rangle_\mu-\mathbb E_\mu\Big[\sum_{u,v\in V}r_v(\sigma)\,(D^+_vr_u)(\sigma)\,D^+_vf(\sigma)\,D^+_uf(\sigma)\Big],$$
--   with $(D^+_vr_u)(\sigma)=r_u(\sigma\cup\{v\})-r_u(\sigma)$.
--
--   The first term on the right is the Dirichlet form, which is nonnegative; the second is the curvature term controlled by the matrices $M_\sigma$ of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), Lemma 2.3, p.8 (PDF p.8)

import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_ip

namespace HardCoreBochner

open scoped BigOperators

/-- **Lemma 2.3** (Bochner-type inequality). Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), Lemma 2.3, p.8.

For every `f : {0,1}^V → ℝ`,
`⟨Lf, Lf⟩_µ ≥ −⟨f, Lf⟩_µ − E_µ[ Σ_{u,v∈V} r_v(σ) (D⁺_v r_u)(σ) D⁺_v f(σ) D⁺_u f(σ) ]`.

**Formalization Note** `(D⁺_v r_u)(σ) = r_u(σ ∪ {v}) − r_u(σ)`; `µ` is a distribution fully supported
on a non-empty downward-closed family (`IsDownClosedLaw`), the standing setting of §2. -/
theorem lemma_2_3 {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (hμ : IsDownClosedLaw μ) (f : (V → Bool) → ℝ) :
    -ip μ f (gen μ f) -
        expect μ (fun σ => ∑ u, ∑ v, rate μ v σ *
          (rate μ u (Function.update σ v true) - rate μ u σ) * Dplus v f σ * Dplus u f σ) ≤
      ip μ (gen μ f) (gen μ f) := by sorry

end HardCoreBochner
