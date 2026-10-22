-- Prove2me | Theorems.Thm_ObservableActions_Reductive_lemma_4_3
-- name    : ObservableActions.Reductive.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:50.058592+00:00
-- url     : https://prove2.me/theorems/4c55874c-dd0b-46b7-ab9b-fb243ad2d513
-- title:
--   Lemma 4.3, p. 13 — Ω(X) = π⁻¹((X//G) ∖ π(X ∖ X_max)); in particular Ω(X) is a G-stable open subset
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a reductive group over $k$ acting regularly on an affine variety $X$, and $\pi:X\to X/\!\!/G$ the categorical quotient, $X/\!\!/G=\operatorname{Spec}k[X]^G$. Let $X_{\max}$ be the set of points whose orbit has maximal dimension, and $\Omega(X)$ the set of points of $X_{\max}$ whose orbit is closed. Then
--   $$\Omega(X)=\pi^{-1}\bigl((X/\!\!/G)\setminus \pi(X\setminus X_{\max})\bigr).$$
--   In particular, $\Omega(X)$ is a (possibly empty) $G$-stable open subset of $X$.
--
--   The lemma describes the locus of closed orbits of maximal dimension through the quotient map. It is the ingredient that makes the condition $\Omega(X)\neq\emptyset$ an open condition, which is how it enters Theorem 4.7.
--
--   **Formalization Note.** Points are $k$-points; $\pi$ is restriction of a point $x:k[X]\to k$ to the invariant subalgebra $k[X]^G$, so $X/\!\!/G$ is the set of $k$-points of $k[X]^G$. No finite generation of $k[X]^G$ is assumed (it holds for reductive $G$). Open means the complement of a common zero locus. $X$ is not assumed irreducible, as in the source.
-- source:
--   Renner–Rittatore, Observable actions of algebraic groups, arXiv:0902.0137v2, p. 13, Lemma 4.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
import Definitions.Def_ObservableActions_Reductive_Defs

namespace ObservableActions.Reductive

open QAlgorithms.Papers.Independent.Support21.P10

universe u v w

/-- Lemma 4.3 (p. 13). For a reductive group acting on an affine variety, with
`π : X → X//G` the categorical quotient (on k-points: restriction to `k[X]^G`),
`Ω(X) = π⁻¹((X//G) ∖ π(X ∖ X_max))`; in particular `Ω(X)` is a (possibly empty)
G-stable open subset. -/
theorem lemma_4_3
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hred : IsReductiveGroup k H)
    (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    omegaLocus rho =
        {x : Point k A | quotientPoint rho x ∉ quotientPoint rho '' (maximalOrbitLocus rho)ᶜ} ∧
      IsClassicallyOpen (omegaLocus rho) ∧
      (∀ g : Point k H, ∀ x ∈ omegaLocus rho, pointAction rho g x ∈ omegaLocus rho) := by sorry

end ObservableActions.Reductive
