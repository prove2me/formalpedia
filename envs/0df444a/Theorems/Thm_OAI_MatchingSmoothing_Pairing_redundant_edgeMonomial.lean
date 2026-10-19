-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_Pairing_redundant_edgeMonomial
-- name    : OAI.MatchingSmoothing.Pairing.redundant_edgeMonomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:50:36.688915+00:00
-- url     : https://prove2.me/theorems/b3ad078a-1075-4e72-8cbf-c511d96609b2
-- title:
--   An edge forced by a partial matching is redundant in an edge monomial
-- statement:
--   Let $V$ be a set and represent the perfect matchings of $V$ as fixed-point-free involutions $N:V\to V$. For an ordered pair $e=(u,v)\in V\times V$ the edge indicator is $x_e(N)=1$ if $N(u)=v$ and $x_e(N)=0$ otherwise. For a finite list $l=(e_1,\dots,e_m)$ of ordered pairs let $x_l=x_{e_1}\cdots x_{e_m}$ be its edge monomial, a function on perfect matchings (the empty list gives the constant $1$); let $\operatorname{supp}(l)\subseteq V$ be the set of all first and second coordinates of the pairs in $l$; and say that $N$ *contains* $l$ if $N(u_i)=v_i$ for every pair $e_i=(u_i,v_i)$ of $l$.
--
--   Let $M$ be a perfect matching of $V$, let $e=(u,v)$ be an ordered pair with $M(u)=v$, and let $l$ be a list contained in $M$. Suppose that $u\in\operatorname{supp}(l)$ or $v\in\operatorname{supp}(l)$. Then, for the list $l'=(e,e_1,\dots,e_m)$ obtained by putting $e$ in front of $l$,
--
--   $$
--   x_{l'}=x_e\,x_l=x_l\qquad\text{as functions on the perfect matchings of }V.
--   $$
--
--   The monomial $x_l$ is the indicator of the set of matchings containing $l$. The theorem says that once a vertex of $e$ is already covered by $l$ and some matching containing $l$ uses $e$, every matching containing $l$ uses $e$, so the factor $x_e$ adds nothing. In computations of symmetrized edge monomials this reduces the inductive step to new edges that avoid the support of $l$.
--
--   **Formalization Note** The monomial is `edgeMonomial l = (l.map edgeCoord).prod`, containment is `ContainsList`, and $\operatorname{supp}(l)$ is `edgeSupport l`. The type `V` is arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/EdgeMonomials.lean#L63-L78

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials

open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing
universe u_1 u_2 u_3
attribute [local instance] Classical.propDecidable
variable {V : Type u_1}

theorem OAI.MatchingSmoothing.Pairing.redundant_edgeMonomial {M : Pairing V} {e : V × V} {l : List (V × V)}
    (he : M.1 e.1 = e.2) (hm : ContainsList M l)
    (hv : e.1 ∈ edgeSupport l ∨ e.2 ∈ edgeSupport l) :
    edgeMonomial (e::l) = edgeMonomial l := by sorry
