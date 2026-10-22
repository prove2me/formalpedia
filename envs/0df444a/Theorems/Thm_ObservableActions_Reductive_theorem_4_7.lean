-- Prove2me | Theorems.Thm_ObservableActions_Reductive_theorem_4_7
-- name    : ObservableActions.Reductive.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:37.683952+00:00
-- url     : https://prove2.me/theorems/fa9654bf-755a-48f5-9ed2-3df50b319a6a
-- title:
--   Theorem 4.7, p. 14 — a reductive action on an irreducible affine variety is observable iff Ω(X) ≠ ∅; the socle is the largest observable closed subset
-- statement:
--   Let $k$ be an algebraically closed field and $G$ a reductive group over $k$ acting regularly on an irreducible affine variety $X$. The action is *observable* if every nonzero $G$-stable ideal $I\subseteq k[X]$ satisfies $I^G\neq(0)$; $\Omega(X)$ is the set of points whose orbit is closed and of maximal dimension; and the socle
--   $$X_{\mathrm{soc}}=\overline{\bigcup_{\overline{\mathcal O(x)}=\mathcal O(x)}\mathcal O(x)}$$
--   is the Zariski closure of the union of the closed orbits. Then:
--
--   1. the action is observable if and only if $\Omega(X)\neq\emptyset$;
--   2. $X_{\mathrm{soc}}$ is the maximum $G$-stable closed subset $Z\subseteq X$ such that the restricted action $G\times Z\to Z$ is observable. That is, $X_{\mathrm{soc}}$ is closed and $G$-stable, the action of $G$ on $k[X_{\mathrm{soc}}]$ induced through the quotient map $k[X]\to k[X_{\mathrm{soc}}]$ exists and is observable, and every $G$-stable closed subset $Z$ on which the induced action is observable satisfies $Z\subseteq X_{\mathrm{soc}}$.
--
--   The theorem gives a geometric description of observability for reductive groups and singles out a canonical closed subvariety, computed from the closed orbits alone, as the largest piece of $X$ on which the action is observable.
--
--   **Formalization Note.** The irreducibility of $X$ (the coordinate ring is a domain) is the paper's standing assumption for §4 (p. 2); without it the first part fails (see the first-sentence milestone). $G$ is not assumed connected, as in the source. No finite generation of $k[X]^G$ is assumed. A restricted action on $Z$ is an action on $k[X]/\mathcal I(Z)$ compatible with the quotient map; it is unique when it exists. For the socle its existence is part of the conclusion; for a competitor $Z$ the hypothesis is that a compatible action exists and is observable. Note that $\Omega(X)\neq\emptyset$ is weaker than "Ω(X) contains a nonempty open subset", the condition of Theorem 3.10.
-- source:
--   Renner–Rittatore, Observable actions of algebraic groups, arXiv:0902.0137v2, p. 14, Theorem 4.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
import Definitions.Def_ObservableActions_Reductive_Defs

namespace ObservableActions.Reductive

open QAlgorithms.Papers.Independent.Support21.P10

universe u v w

/-- Theorem 4.7 (p. 14). Let a reductive group act on an irreducible affine variety
`X`. The action is observable if and only if `Ω(X) ≠ ∅`. Moreover `X_soc` is the
maximum G-stable closed subset `Z ⊆ X` such that the restricted action
`G × Z → Z` is observable: `X_soc` is closed and G-stable, the restricted action on it
exists and is observable, and every G-stable closed `Z` with observable restricted
action is contained in `X_soc`. -/
theorem theorem_4_7
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hred : IsReductiveGroup k H)
    (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    (IsObservable rho ↔ (omegaLocus rho).Nonempty) ∧
      classicalClosure (socle rho) = socle rho ∧
      (∀ g : Point k H, ∀ x ∈ socle rho, pointAction rho g x ∈ socle rho) ∧
      (∃ rhoS : Point k H →* ((A ⧸ coordinateVanishingIdeal (k := k) (socle rho)) ≃ₐ[k]
          (A ⧸ coordinateVanishingIdeal (k := k) (socle rho))),
        IsRestrictionOf rho (socle rho) rhoS ∧ IsObservable rhoS) ∧
      (∀ Z : Set (Point k A), classicalClosure Z = Z →
        (∀ g : Point k H, ∀ x ∈ Z, pointAction rho g x ∈ Z) →
        ∀ rhoZ : Point k H →* ((A ⧸ coordinateVanishingIdeal (k := k) Z) ≃ₐ[k]
            (A ⧸ coordinateVanishingIdeal (k := k) Z)),
          IsRestrictionOf rho Z rhoZ → IsObservable rhoZ → Z ⊆ socle rho) := by sorry

end ObservableActions.Reductive
