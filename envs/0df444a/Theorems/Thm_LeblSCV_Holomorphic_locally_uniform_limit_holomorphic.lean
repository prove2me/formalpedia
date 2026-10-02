-- Prove2me | Theorems.Thm_LeblSCV_Holomorphic_locally_uniform_limit_holomorphic
-- name    : LeblSCV.Holomorphic.locally_uniform_limit_holomorphic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:10:41.8884+00:00
-- url     : https://prove2.me/theorems/57f68643-1b07-4080-b9eb-e5d14be88603
-- title:
--   Proposition 1.2.3 — uniform limits on compact sets of holomorphic functions
-- statement:
--   Let $U \subset \mathbb{C}^n$ be an open set, and suppose the sequence of holomorphic functions $f_\ell : U \to \mathbb{C}$ ($\ell \in \mathbb{N}$) converges uniformly on compact subsets of $U$ to $f : U \to \mathbb{C}$. Then $f$ is holomorphic, and for every multi-index $\alpha$,
--   $$\frac{\partial^{|\alpha|} f_\ell}{\partial z^\alpha} \longrightarrow \frac{\partial^{|\alpha|} f}{\partial z^\alpha}$$
--   uniformly on compact subsets of $U$.
--
--   **Formalization Note.** "Uniformly on compact subsets" is `TendstoUniformlyOn … atTop K` for every compact `K ⊆ U`; holomorphy is Definition 1.1.2 and $\partial^{|\alpha|}/\partial z^\alpha$ is the iterated Wirtinger derivative.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 23, Proposition 1.2.3

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_wirtingerIter

open Filter

namespace LeblSCV.Holomorphic

/-- Proposition 1.2.3 (Lebl, p. 23). Let `U ⊆ ℂⁿ` be open and let `f_ℓ` (`ℓ ∈ ℕ`) be holomorphic
functions on `U` converging to `f` uniformly on compact subsets of `U`. Then `f` is holomorphic on
`U`, and for every multi-index `α` the derivatives `∂^{|α|} f_ℓ / ∂z^α` converge to
`∂^{|α|} f / ∂z^α` uniformly on compact subsets of `U`. -/
theorem locally_uniform_limit_holomorphic {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (F : ℕ → (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) → ℂ)
    (hconv : ∀ K ⊆ U, IsCompact K → TendstoUniformlyOn F f atTop K)
    (hF : ∀ ℓ, IsHolomorphicOn (F ℓ) U) :
    IsHolomorphicOn f U ∧
      ∀ α : Fin n → ℕ, ∀ K ⊆ U, IsCompact K →
        TendstoUniformlyOn (fun ℓ => wirtingerIter α (F ℓ)) (wirtingerIter α f) atTop K := by sorry

end LeblSCV.Holomorphic
