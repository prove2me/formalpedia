-- Prove2me | Theorems.Thm_ObservableActions_Reductive_theorem_4_7_first
-- name    : ObservableActions.Reductive.theorem_4_7_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:33.843571+00:00
-- url     : https://prove2.me/theorems/f57d0561-80d9-419c-a915-fe715c133d4e
-- title:
--   Theorem 4.7, p. 14, first sentence — a reductive action on an irreducible affine variety is observable iff Ω(X) ≠ ∅
-- statement:
--   Let $k$ be an algebraically closed field and $G$ a reductive group over $k$ acting regularly on an irreducible affine variety $X$. Recall that the action is *observable* if every nonzero $G$-stable ideal $I\subseteq k[X]$ contains a nonzero invariant, $I^G\neq(0)$, and that $\Omega(X)$ is the set of points whose orbit is closed and of maximal dimension. Then
--   $$\text{the action is observable}\iff \Omega(X)\neq\emptyset .$$
--
--   For general affine groups observability needs two conditions (Theorem 3.10); for reductive groups it reduces to the existence of a single closed orbit of maximal dimension. The proof of the second sentence of Theorem 4.7 applies this to the socle and to irreducible closed $G$-stable subsets.
--
--   **Formalization Note.** The irreducibility of $X$ (the coordinate ring is a domain) is the paper's standing assumption for §4 (p. 2); without it the statement fails: $\mathbb G_m$ acting on $\mathbb G_m\sqcup\mathbb A^1$, by translation on the first piece and with weight one on the second, has $\Omega(X)\neq\emptyset$ but the stable ideal $0\times(t)$ contains no nonzero invariant. $G$ is not assumed connected, as in the source.
-- source:
--   Renner–Rittatore, Observable actions of algebraic groups, arXiv:0902.0137v2, p. 14, Theorem 4.7, first sentence

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
import Definitions.Def_ObservableActions_Reductive_Defs

namespace ObservableActions.Reductive

open QAlgorithms.Papers.Independent.Support21.P10

universe u v w

/-- Theorem 4.7, first sentence (p. 14). A reductive group acting on an irreducible
affine variety `X` acts observably if and only if `Ω(X) ≠ ∅`. -/
theorem theorem_4_7_first
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hred : IsReductiveGroup k H)
    (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    IsObservable rho ↔ (omegaLocus rho).Nonempty := by sorry

end ObservableActions.Reductive
