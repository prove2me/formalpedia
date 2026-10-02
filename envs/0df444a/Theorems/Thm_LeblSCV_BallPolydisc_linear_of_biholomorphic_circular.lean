-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_linear_of_biholomorphic_circular
-- name    : LeblSCV.BallPolydisc.linear_of_biholomorphic_circular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:22:59.623491+00:00
-- url     : https://prove2.me/theorems/773dd775-d7cb-4cda-875a-a64207ba2867
-- title:
--   Corollary 1.5.2 — origin-preserving biholomorphisms of bounded circular domains are linear
-- statement:
--   Let $U, V \subset \mathbb{C}^n$ be bounded circular domains with $0 \in U$ and $0 \in V$, and let $f : U \to V$ be a biholomorphic map with $f(0) = 0$. Then $f$ is linear: there is a $\mathbb{C}$-linear map $L : \mathbb{C}^n \to \mathbb{C}^n$ with
--   $$f(z) = L z \quad \text{for all } z \in U.$$
--
--   In particular every automorphism of the ball $\mathbb{B}_n$ fixing the origin is linear (in fact unitary), and likewise for polydiscs centred at the origin; this is the first step in computing these automorphism groups.
--
--   **Formalization Note.** A circular domain is `IsCircularDomain` (open, connected, nonempty, invariant under $z \mapsto e^{i\theta} z$); bounded is `Bornology.IsBounded`; biholomorphic is `IsBiholomorphicMap f U V` (Definition 1.4.1 with `DifferentiableOn ℂ`). "Linear" is the restriction to $U$ of a `ℂ`-linear map `(Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 39, Corollary 1.5.2

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsCircularDomain
import Definitions.Def_LeblSCV_BallPolydisc_IsBiholomorphicMap

namespace LeblSCV.BallPolydisc

/-- Corollary 1.5.2 (Lebl, p. 39). If `U, V ⊆ ℂⁿ` are bounded circular domains containing `0`
and `f : U → V` is a biholomorphic map with `f(0) = 0`, then `f` is linear: it is the
restriction to `U` of a `ℂ`-linear map `ℂⁿ → ℂⁿ`. -/
theorem linear_of_biholomorphic_circular {n : ℕ} (U V : Set (Fin n → ℂ))
    (hU : IsCircularDomain U) (hV : IsCircularDomain V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hU0 : (0 : Fin n → ℂ) ∈ U) (hV0 : (0 : Fin n → ℂ) ∈ V)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (hf : IsBiholomorphicMap f U V) (hf0 : f 0 = 0) :
    ∃ L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ), ∀ z ∈ U, f z = L z := by sorry

end LeblSCV.BallPolydisc
