-- Prove2me | Theorems.Thm_ObservableActions_Reductive_theorem_4_6_moreover
-- name    : ObservableActions.Reductive.theorem_4_6_moreover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:34.391524+00:00
-- url     : https://prove2.me/theorems/2da375d0-912e-45e7-81f3-00b00d201011
-- title:
--   Theorem 4.6, p. 13, "Moreover" sentence — if π|_Z is dominant then X_soc ⊆ Z, X_soc is irreducible and Ω(X_soc) ≠ ∅
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a reductive group over $k$ acting regularly on an irreducible affine variety $X$, $\pi:X\to X/\!\!/G$ the categorical quotient, and $X_{\mathrm{soc}}$ the socle, the closure of the union of the closed orbits. Let $Z\subseteq X$ be a $G$-stable closed subset such that $\pi|_Z:Z\to X/\!\!/G$ is dominant. Then
--
--   1. $X_{\mathrm{soc}}\subseteq Z$;
--   2. $X_{\mathrm{soc}}$ is irreducible;
--   3. $\Omega(X_{\mathrm{soc}})\neq\emptyset$: for the action of $G$ restricted to $X_{\mathrm{soc}}$, some orbit is closed and of maximal dimension among the orbits in $X_{\mathrm{soc}}$.
--
--   This is the "Moreover" sentence of Theorem 4.6. Applied with $Z=X$ it shows that the socle is an irreducible closed $G$-stable subvariety with a closed orbit of maximal dimension, the input to the second sentence of Theorem 4.7.
--
--   **Formalization Note.** The irreducibility of $X$ (the coordinate ring is a domain) is the paper's standing assumption for §4 (p. 2: "a reductive group $G$ acting on the irreducible, affine variety $X$"); without it the irreducibility of $X_{\mathrm{soc}}$ fails (two points with the trivial group). Dominance is $\overline{\pi(Z)}=X/\!\!/G$ in the $k$-points of $k[X]^G$. The restricted action on $k[X_{\mathrm{soc}}]=k[X]/\mathcal I(X_{\mathrm{soc}})$ is asserted to exist (it is the action induced through the quotient map), and $\Omega$ is computed for that action, not as $\Omega(X)\cap X_{\mathrm{soc}}$. The first sentence of Theorem 4.6 (bijectivity and pure inseparability of $Z/\!\!/G\to X/\!\!/G$) is not formalized here.
-- source:
--   Renner–Rittatore, Observable actions of algebraic groups, arXiv:0902.0137v2, p. 13, Theorem 4.6, "Moreover" sentence

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
import Definitions.Def_ObservableActions_Reductive_Defs

namespace ObservableActions.Reductive

open QAlgorithms.Papers.Independent.Support21.P10

universe u v w

/-- Theorem 4.6, "Moreover" sentence (p. 13). Let a reductive group act on an
irreducible affine variety `X` and let `Z ⊆ X` be a G-stable closed subset such that
`π|_Z : Z → X//G` is dominant. Then `X_soc ⊆ Z`, `X_soc` is irreducible, and
`Ω(X_soc) ≠ ∅` for the restricted action of `G` on `X_soc`. -/
theorem theorem_4_6_moreover
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hred : IsReductiveGroup k H)
    (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    ∀ Z : Set (Point k A), classicalClosure Z = Z →
      (∀ g : Point k H, ∀ x ∈ Z, pointAction rho g x ∈ Z) →
      classicalClosure (quotientPoint rho '' Z) = Set.univ →
      socle rho ⊆ Z ∧
        (coordinateVanishingIdeal (k := k) (socle rho)).IsPrime ∧
        ∃ rhoS : Point k H →* ((A ⧸ coordinateVanishingIdeal (k := k) (socle rho)) ≃ₐ[k]
            (A ⧸ coordinateVanishingIdeal (k := k) (socle rho))),
          IsRestrictionOf rho (socle rho) rhoS ∧ (omegaLocus rhoS).Nonempty := by sorry

end ObservableActions.Reductive
