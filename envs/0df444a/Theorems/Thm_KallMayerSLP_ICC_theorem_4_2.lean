-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_theorem_4_2
-- name    : KallMayerSLP.ICC.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:40.670084+00:00
-- url     : https://prove2.me/theorems/65437d3e-b394-4da9-88d8-279ec1d3f6f7
-- title:
--   Theorem 4.2 — $\hat{\mathcal S}(\alpha)$ is polyhedral for finite discrete $\xi$ (corrected: $\alpha\in[0,\tfrac12]$ replaces the printed "$\gamma\ge 0$, $\mathcal S(\gamma)$")
-- statement:
--   Let $\xi$ have the finite discrete distribution (4.7), with $t^k=t(\hat\xi^k)$, $h^k=h(\hat\xi^k)$, $\bar t=\mathbb E_\xi[t(\xi)]$, $\bar h=\mathbb E_\xi[h(\xi)]$. For $\alpha\in[0,\tfrac12]$, the set $\hat{\mathcal S}(\alpha)=\{x\mid K_\alpha(x)\le 0\}$ is polyhedral, and
--   $$
--   \{x\mid K_\alpha(x)\le 0\}=\bigcap_{\mathcal K\subset\mathcal N}\Big\{x\ \Big|\ (1-2\alpha)\sum_{k\in\mathcal K}p_k(t^kx-h^k)+\alpha(\bar t x-\bar h)\le 0\Big\}.
--   $$
--   This gives the $\alpha$-variant of integrated chance constraints the same finite linear description as Theorem 4.1.
--
--   **Formalization Note** $K_\alpha$, $\bar t$, $\bar h$ are expectations against the law (4.7). The sentence before the theorem in the book fixes $\alpha\in[0,\tfrac12]$ and $\hat{\mathcal S}(\alpha)$.
--
--   Differences from the source:
--
--   - correction: "For γ ≥ 0, 𝒮(γ) is a polyhedral set" with the representation of {x | K_α(x) ≤ 0} → α ∈ [0, ½] and Ŝ(α) polyhedral, with that representation; reason: the hypothesis is copied from Theorem 4.1 and the preceding sentence fixes α ∈ [0, ½]; without it the representation is false at N = 1, p₁ = 1, t¹ = 1, h¹ = 0, α = 1, where the left side is ℝ and the right side is (−∞, 0]
--   - generalization: ξ with realizations in ℝʳ, t(ξ), h(ξ) affine in ξ (1.2) → Ξ any measurable space with measurable singletons, t, h arbitrary functions, atoms not required distinct; reason: the book says (1.2) is not used in the chapter; Ξ = ℝʳ with its Borel sets gives the book's case
--   - encoding: 𝒦 ⊂ 𝒩 over subsets of {1, …, N} → 𝒦 : Finset (Fin N), all subsets including ∅ and the whole set; reason: the book includes 𝒦 = ∅ with empty sum 0 (p.153); 0-based indices; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 4.2, p.154 (PDF 164)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_Polyhedron
import Definitions.Def_KallMayerSLP_ICC_KAlpha
import Definitions.Def_KallMayerSLP_ICC_discreteLaw

open MeasureTheory Matrix

namespace KallMayerSLP.ICC

/-- **Theorem 4.2 (the `α`-variant, finite discrete distribution), corrected hypothesis.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Theorem 4.2, p.154 (PDF 164). For
`α ∈ [0, ½]`, `Ŝ(α) = {x | K_α(x) ≤ 0}` is a polyhedral set, and
`{x | K_α(x) ≤ 0} = ⋂_{𝒦 ⊂ 𝒩} {x | (1 − 2α) Σ_{k∈𝒦} p_k (tᵏx − hᵏ) + α(t̄x − h̄) ≤ 0}`.

**Formalization Note.** The book prints "For `γ ≥ 0`, `S(γ)` is a polyhedral set", which is copied
from Theorem 4.1; the sentence before it fixes `α ∈ [0, ½]` and `Ŝ(α)`. The hypothesis on `α` is
needed: the representation fails for `α > ½` (`N = 1`, `p₁ = 1`, `t¹ = 1`, `h¹ = 0`, `α = 1`).
`t̄`, `h̄` are the expectations against the law (4.7). -/
theorem theorem_4_2 {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ] {N n : ℕ}
    (p : Fin N → ℝ) (ξhat : Fin N → Ξ) (hp : ∀ k, 0 < p k) (hsum : ∑ k, p k = 1)
    (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ) (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1 / 2) :
    VanderbeiLP.StrictComp.IsPolyhedron {x | KAlpha (discreteLaw p ξhat) t h α x ≤ 0} ∧
    {x | KAlpha (discreteLaw p ξhat) t h α x ≤ 0} =
      ⋂ 𝒦 : Finset (Fin N),
        {x | (1 - 2 * α) * ∑ k ∈ 𝒦, p k * (t (ξhat k) ⬝ᵥ x - h (ξhat k)) +
          α * ((∫ ξ, t ξ ∂(discreteLaw p ξhat)) ⬝ᵥ x - ∫ ξ, h ξ ∂(discreteLaw p ξhat)) ≤ 0} := by sorry

end KallMayerSLP.ICC
