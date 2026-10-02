-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_cartan_uniqueness
-- name    : LeblSCV.BallPolydisc.cartan_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:22:20.158987+00:00
-- url     : https://prove2.me/theorems/21c904d7-4d7d-45ed-8846-0c3de2df84c7
-- title:
--   Theorem 1.5.1 (Cartan) — uniqueness theorem for self-maps of bounded domains
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a bounded domain, $a \in U$, and $f : U \to U$ a holomorphic mapping with $f(a) = a$ whose derivative $Df(a)$ is the identity. Then
--   $$f(z) = z \quad \text{for all } z \in U.$$
--
--   This is a several-variable analogue of the Schwarz lemma: a self-map of a bounded domain that agrees with the identity to first order at one point is the identity. It is the tool used to compute automorphism groups (Corollary 1.5.2). Boundedness is essential: on $\mathbb{C}^n$ the map $z \mapsto z + (z_1^2, 0, \dots, 0)$ is a counterexample.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; bounded is `Bornology.IsBounded U` (independent of the norm); a domain is open, connected and nonempty. Holomorphic is `DifferentiableOn ℂ f U`; $f(U) \subset U$ is `Set.MapsTo f U U`. $Df(a)$ is the complex Fréchet derivative `fderiv ℂ f a`, and "is the identity" is `fderiv ℂ f a = ContinuousLinearMap.id ℂ _`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 37, Theorem 1.5.1

import Mathlib

namespace LeblSCV.BallPolydisc

/-- Theorem 1.5.1 (Cartan; Lebl, p. 37). If `U ⊆ ℂⁿ` is a bounded domain, `a ∈ U`,
`f : U → U` is holomorphic, `f(a) = a` and `Df(a)` is the identity, then `f(z) = z` on `U`. -/
theorem cartan_uniqueness {n : ℕ} (U : Set (Fin n → ℂ))
    (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (a : Fin n → ℂ) (ha : a ∈ U) (f : (Fin n → ℂ) → (Fin n → ℂ))
    (hf : DifferentiableOn ℂ f U) (hfU : Set.MapsTo f U U) (hfa : f a = a)
    (hDf : fderiv ℂ f a = ContinuousLinearMap.id ℂ (Fin n → ℂ)) :
    ∀ z ∈ U, f z = z := by sorry

end LeblSCV.BallPolydisc
