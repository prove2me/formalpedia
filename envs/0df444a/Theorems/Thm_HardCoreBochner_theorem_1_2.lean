-- Prove2me | Theorems.Thm_HardCoreBochner_theorem_1_2
-- name    : HardCoreBochner.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:39.769901+00:00
-- url     : https://prove2.me/theorems/c6ece660-f7f1-4fa9-a76c-f28b4ad7df9f
-- title:
--   Theorem 1.2 — positive semidefinite $M_\sigma$ gives spectral gap at least $\delta$
-- statement:
--   Let $V$ be finite, let $X\subseteq\{0,1\}^V$ be a non-empty downward-closed set family and let $\mu$ be a distribution fully supported on $X$. Suppose that for $\delta\in(0,1)$ and every $\sigma\in X$ the matrix $M_\sigma\in\mathbb R^{V\times V}$,
--   $$M_\sigma(u,v)=(1-\delta)\,r_v(\sigma)\,\mathbf 1_{u=v}-r_v(\sigma)\big(r_u(\sigma\cup\{v\})-r_u(\sigma)\big),\tag{3}$$
--   is positive semidefinite. Then continuous-time Glauber dynamics for $\mu$ has spectral gap at least $\delta$: for every $f:\{0,1\}^V\to\mathbb R$,
--   $$\delta\,\mathrm{Var}_\mu(f)\le\langle f,-Lf\rangle_\mu.$$
--
--   This is the paper's version of [8, Theorem 1.9]; applied to the hard-core model it yields Theorem 1.1.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
--   - encoding: M_σ positive semidefinite → 0 ≤ x ⬝ᵥ M_σ *ᵥ x for every x : V → ℝ; reason: this is the quadratic-form meaning of positive semidefinite; M_σ is symmetric on X, so it equals PosSemidef there
--   - encoding: spectral gap γ(L) ≥ δ, γ(L) the infimum (2) of ⟨f, −Lf⟩_µ/Var_µ(f) over non-constant f → δ Var_µ(f) ≤ ⟨f, −Lf⟩_µ for every f : (V → Bool) → ℝ; reason: γ(L) is the largest δ with this inequality for all f; the inequality form has no 0/0 for f constant on X and no empty infimum
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), Theorem 1.2, (3), p.3 (PDF p.3)

import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_ip
import Definitions.Def_HardCoreBochner_Mmat

namespace HardCoreBochner

open scoped BigOperators
open Matrix

/-- **Theorem 1.2.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), Theorem 1.2, p.3.

Let `X ⊆ {0,1}^V` be a non-empty downward-closed set family and `µ` a distribution fully supported
on `X`. Suppose that for `δ ∈ (0,1)` and all `σ ∈ X` the matrix
`M_σ(u, v) = (1 − δ) r_v(σ) 1_{u=v} − r_v(σ)(r_u(σ ∪ {v}) − r_u(σ))` is positive semidefinite. Then
continuous-time Glauber dynamics for `µ` has spectral gap at least `δ`: for every `f`,
`δ Var_µ(f) ≤ ⟨f, −Lf⟩_µ`.

**Formalization Note** `X` is the support of `µ` (`IsDownClosedLaw`). Positive semidefiniteness is
`0 ≤ x ⬝ᵥ M_σ *ᵥ x` for all `x`. "Spectral gap at least δ" (`γ(L) ≥ δ` with `γ` the infimum (2) over
non-constant `f`) is stated as the Poincaré inequality it means. -/
theorem theorem_1_2 {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (hμ : IsDownClosedLaw μ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : ∀ σ, 0 < μ σ → ∀ x : V → ℝ, 0 ≤ x ⬝ᵥ (Mmat μ δ σ *ᵥ x)) (f : (V → Bool) → ℝ) :
    δ * var μ f ≤ ip μ f (fun σ => -gen μ f σ) := by sorry

end HardCoreBochner
