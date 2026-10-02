-- Prove2me | Theorems.Thm_LeblSCV_Holomorphic_maximum_principle
-- name    : LeblSCV.Holomorphic.maximum_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:14:15.49503+00:00
-- url     : https://prove2.me/theorems/36a8f8db-b59a-4444-be82-26bf9b184b85
-- title:
--   Theorem 1.2.8 — maximum principle
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain and let $f : U \to \mathbb{C}$ be holomorphic. If $|f(z)|$ attains a local maximum at some $a \in U$, then
--   $$f \equiv f(a) \quad \text{on } U.$$
--
--   **Formalization Note.** A domain is `IsOpen U ∧ IsConnected U`. "Local maximum at $a$" is `IsLocalMaxOn (fun z => ‖f z‖) U a`: $|f(z)| \le |f(a)|$ for all $z \in U$ near $a$ (as $U$ is open this is an ordinary local maximum). Holomorphy is Definition 1.1.2.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 25, Theorem 1.2.8

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn

namespace LeblSCV.Holomorphic

/-- Theorem 1.2.8 (Maximum principle, Lebl, p. 25). Let `U ⊆ ℂⁿ` be a domain and `f` holomorphic
on `U`. If `|f|` attains a local maximum (relative to `U`) at some `a ∈ U`, then `f ≡ f(a)` on `U`. -/
theorem maximum_principle {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hUc : IsConnected U)
    {f : (Fin n → ℂ) → ℂ} (hf : IsHolomorphicOn f U)
    {a : Fin n → ℂ} (ha : a ∈ U) (hmax : IsLocalMaxOn (fun z => ‖f z‖) U a) :
    ∀ z ∈ U, f z = f a := by sorry

end LeblSCV.Holomorphic
