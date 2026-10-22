-- Prove2me | Theorems.Thm_ObservableActions_Reductive_proposition_4_4
-- name    : ObservableActions.Reductive.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:43.973908+00:00
-- url     : https://prove2.me/theorems/15701a60-d1c6-4bee-8242-92a8c28471f1
-- title:
--   Proposition 4.4 (Popov), p. 13 — if Ω(X) ≠ ∅ then Ω(X) is open
-- statement:
--   Let $k$ be an algebraically closed field and $G$ a reductive group over $k$ acting regularly on an affine variety $X$. Let $\Omega(X)$ be the set of points $x$ whose orbit $\mathcal O(x)$ is closed and of maximal dimension among all orbits. If $\Omega(X)\neq\emptyset$, then
--   $$\Omega(X)\ \text{is an open subset of } X.$$
--
--   This is Popov's theorem on the stability of actions; it is the form of openness that the proof of Theorem 4.7 cites, and it rephrases condition (2) of Theorem 3.10 for reductive groups.
--
--   **Formalization Note.** Open means the complement of a common zero locus of coordinate functions. $X$ is not assumed irreducible, as in the source.
-- source:
--   Renner–Rittatore, Observable actions of algebraic groups, arXiv:0902.0137v2, p. 13, Proposition 4.4 (citing Popov [14, Theorem 4])

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
import Definitions.Def_ObservableActions_Reductive_Defs

namespace ObservableActions.Reductive

open QAlgorithms.Papers.Independent.Support21.P10

universe u v w

/-- Proposition 4.4 (Popov; p. 13). For a reductive group acting on an affine variety
with `Ω(X) ≠ ∅`, the set `Ω(X)` is open. -/
theorem proposition_4_4
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hred : IsReductiveGroup k H)
    (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    (omegaLocus rho).Nonempty → IsClassicallyOpen (omegaLocus rho) := by sorry

end ObservableActions.Reductive
