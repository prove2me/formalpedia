-- Prove2me | Theorems.Thm_ObservableActions_Reductive_lemma_4_5
-- name    : ObservableActions.Reductive.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:31.775285+00:00
-- url     : https://prove2.me/theorems/1e41e7d9-bb43-4b14-b102-0519ea9db1bb
-- title:
--   Lemma 4.5, p. 13 — π on X ∖ X_max is dominant ⇔ surjective ⇔ X_max has no closed orbit ⇔ Ω(X) = ∅
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a reductive group over $k$ acting regularly on an affine variety $X$, and $\pi:X\to X/\!\!/G$ the categorical quotient. Let $X_{\max}$ be the set of points whose orbit has maximal dimension and $\Omega(X)\subseteq X_{\max}$ the subset of those whose orbit is closed. The following are equivalent:
--
--   1. the restriction $\pi|_{X\setminus X_{\max}}:X\setminus X_{\max}\to X/\!\!/G$ is dominant, i.e. $\overline{\pi(X\setminus X_{\max})}=X/\!\!/G$;
--   2. the restriction $\pi|_{X\setminus X_{\max}}$ is surjective;
--   3. $X_{\max}$ does not contain any closed orbit;
--   4. $\Omega(X)=\emptyset$.
--
--   The lemma turns the non-emptiness of $\Omega(X)$ into a statement about the image of the lower-dimensional orbits in the quotient. It is used in Theorem 4.6 to show that the socle carries a closed orbit of maximal dimension.
--
--   **Formalization Note.** $X/\!\!/G$ is the set of $k$-points of $k[X]^G$ and $\pi$ is restriction of points; the closure is the Zariski closure in those $k$-points. Conditions (3) and (4) coincide by the definition of $\Omega(X)$; the content is the equivalence with (1) and (2). $X$ is not assumed irreducible, as in the source.
-- source:
--   Renner–Rittatore, Observable actions of algebraic groups, arXiv:0902.0137v2, p. 13, Lemma 4.5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
import Definitions.Def_ObservableActions_Reductive_Defs

namespace ObservableActions.Reductive

open QAlgorithms.Papers.Independent.Support21.P10

universe u v w

/-- Lemma 4.5 (p. 13). For a reductive group acting on an affine variety, with
`π : X → X//G` the categorical quotient, the following are equivalent:
(1) `π` restricted to `X ∖ X_max` is dominant; (2) it is surjective;
(3) `X_max` contains no closed orbit; (4) `Ω(X) = ∅`. -/
theorem lemma_4_5
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hred : IsReductiveGroup k H)
    (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    [classicalClosure (quotientPoint rho '' (maximalOrbitLocus rho)ᶜ) = Set.univ,
      quotientPoint rho '' (maximalOrbitLocus rho)ᶜ = Set.univ,
      ∀ x ∈ maximalOrbitLocus rho, ¬ IsClosedOrbit rho x,
      omegaLocus rho = ∅].TFAE := by sorry

end ObservableActions.Reductive
