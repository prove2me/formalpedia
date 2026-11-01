-- Prove2me | Theorems.Thm_Grunbaum2003_schemeRealizes_unique_combinatorial_type
-- name    : Grunbaum2003.schemeRealizes_unique_combinatorial_type
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:29.892809+00:00
-- url     : https://prove2.me/theorems/7aea586b-9ddf-4413-9353-bef3af480304
-- title:
--   Uniqueness of combinatorial type for polytopes realizing a vertex-face scheme
-- statement:
--   This theorem proves that a finite vertex-face incidence scheme uniquely determines the combinatorial type (face lattice up to order isomorphism) of any polytope that realizes it.
--
--   Let $d_1, d_2, k \in \mathbb{N}$, let $S$ be a finite vertex-face incidence scheme represented as a list of vertex-index lists (`List (List ℕ)`), and let $P \subseteq \mathbb{R}^{d_1}$ and $Q \subseteq \mathbb{R}^{d_2}$ be polytopes that both realize $S$ on $k$ vertices (`SchemeRealizes k S P` and `SchemeRealizes k S Q`). Then their face lattices are order-isomorphic:
--
--   $$
--   \operatorname{SchemeRealizes}(k, S, P) \;\land\; \operatorname{SchemeRealizes}(k, S, Q) \implies \mathcal{F}(P) \simeq_{\mathrm{ord}} \mathcal{F}(Q).
--   $$
--
--   In Grünbaum's framework (§5.5, Theorem 5.5.2), enumerating combinatorial types of polytopes proceeds by enumerating finite abstract schemes $S$ and testing whether $S$ is geometrically realizable. This theorem establishes the uniqueness half of that reduction: any two geometric realizations of the same scheme $S$ have isomorphic face posets.
--
--   **Formalization Note** Under `SchemeRealizes k S P`, the vertices of $P$ are indexed by $V_P : \operatorname{Fin} k \to (\operatorname{Fin} d_1 \to \mathbb{R})$, and the subsets of $\{0,\dots,k-1\}$ cut out by faces $F \in \mathcal{F}(P)$ are precisely $\emptyset$, $\{0,\dots,k-1\}$, and the finsets appearing in $S$, ordered by inclusion.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.2 & §5.5, pp. 36, 90–91, Theorem 5.5.2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Mathlib.Order.Hom.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem schemeRealizes_unique_combinatorial_type (d₁ d₂ k : ℕ) (S : List (List ℕ))
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (hP : SchemeRealizes k S P) (hQ : SchemeRealizes k S Q) :
    Nonempty (PolytopeFace P ≃o PolytopeFace Q) := by sorry

end Grunbaum2003
