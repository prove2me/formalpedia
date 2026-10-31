-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_theorem_4_1
-- name    : KallMayerSLP.ICC.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:04.869985+00:00
-- url     : https://prove2.me/theorems/c307bbba-a30a-4d88-814d-5200f5dbacf4
-- title:
--   Theorem 4.1 — the separate integrated chance constraint is polyhedral for finite discrete $\xi$
-- statement:
--   Let $\xi$ have the finite discrete distribution (4.7), with realizations $\hat\xi^k$ and probabilities $p_k>0$, $\sum_k p_k=1$, and put $t^k=t(\hat\xi^k)$, $h^k=h(\hat\xi^k)$, $\mathcal N=\{1,\dots,N\}$. For $\gamma\ge 0$, the set $\mathcal S(\gamma)=\{x\mid K(x)\le\gamma\}$ is polyhedral, and
--   $$
--   \{x\mid K(x)\le\gamma\}=\bigcap_{\mathcal K\subset\mathcal N}\Big\{x\ \Big|\ \sum_{k\in\mathcal K}p_k(t^kx-h^k)\le\gamma\Big\}.
--   $$
--   For $\mathcal K=\emptyset$ the sum is $0$. So the constraint is a system of $2^N-1$ proper linear inequalities, which is the representation used in dual decomposition.
--
--   **Formalization Note** $K$ is the expectation against the law (4.7), not a sum by definition. "Polyhedral" means a finite intersection of closed half-spaces of $\mathbb R^n$, possibly with zero coefficient vectors, via the published `IsPolyhedron`.
--
--   Differences from the source:
--
--   - generalization: ξ with realizations in ℝʳ, t(ξ), h(ξ) affine in ξ (1.2) → Ξ any measurable space with measurable singletons, t, h arbitrary functions, atoms not required distinct; reason: the book says (1.2) is not used in the chapter; Ξ = ℝʳ with its Borel sets gives the book's case
--   - encoding: 𝒦 ⊂ 𝒩 over subsets of {1, …, N} → 𝒦 : Finset (Fin N), all subsets including ∅ and the whole set; reason: the book includes 𝒦 = ∅ with empty sum 0 (p.153); 0-based indices; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 4.1 and (4.12), p.152 (PDF 162)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_Polyhedron
import Definitions.Def_KallMayerSLP_ICC_K
import Definitions.Def_KallMayerSLP_ICC_discreteLaw

open MeasureTheory Matrix

namespace KallMayerSLP.ICC

/-- **Theorem 4.1 (separate integrated chance constraints, finite discrete distribution).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Theorem 4.1 and (4.12), p.152
(PDF 162). For `γ ≥ 0`, `S(γ) = {x | K(x) ≤ γ}` is a polyhedral set, and
`{x | K(x) ≤ γ} = ⋂_{𝒦 ⊂ 𝒩} {x | Σ_{k∈𝒦} p_k (tᵏx − hᵏ) ≤ γ}`.

**Formalization Note.** `ξ` has the law (4.7), `tᵏ = t(ξ̂ᵏ)`, `hᵏ = h(ξ̂ᵏ)`. `K` is the expectation
against that law, not a sum by definition. `𝒦` runs over all subsets of `𝒩` including `∅`, where
the sum is `0` (p.153). `MeasurableSingletonClass Ξ` holds for the book's `Ξ ⊂ ℝʳ` with the Borel
σ-algebra; it makes every function integrable against the law. -/
theorem theorem_4_1 {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ] {N n : ℕ}
    (p : Fin N → ℝ) (ξhat : Fin N → Ξ) (hp : ∀ k, 0 < p k) (hsum : ∑ k, p k = 1)
    (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ) (γ : ℝ) (hγ : 0 ≤ γ) :
    VanderbeiLP.StrictComp.IsPolyhedron {x | K (discreteLaw p ξhat) t h x ≤ γ} ∧
    {x | K (discreteLaw p ξhat) t h x ≤ γ} =
      ⋂ 𝒦 : Finset (Fin N), {x | ∑ k ∈ 𝒦, p k * (t (ξhat k) ⬝ᵥ x - h (ξhat k)) ≤ γ} := by sorry

end KallMayerSLP.ICC
