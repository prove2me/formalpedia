-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_tableGamma_rowsum
-- name    : OAI.MatchingSmoothing.tableGamma_rowsum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:37:56.056953+00:00
-- url     : https://prove2.me/theorems/8ce8c38b-7de1-4cc1-8c77-a2893255e526
-- title:
--   The vertex colour distribution is the marginal of the symmetrised pair-colour table
-- statement:
--   Let $H$ be a finite set and $V=H\times\{0,1\}$, with standard pairs $\{(i,0),(i,1)\}$, and let $f:V\to\{0,1,2\}$ be a $3$-colouring. The *type* of an ordered colour pair $(a,b)$ is the unordered pair $\{a,b\}$, a multiset, so there are six types. The multiplicity $m(\{a,b\})$ of a type is the number of ordered pairs of that type: $1$ if $a=b$ and $2$ otherwise. The *table* of $f$ counts standard pairs by type,
--
--   $$
--   T_f(\{a,b\})=\#\{i\in H:\ \{f(i,0),f(i,1)\}=\{a,b\}\}.
--   $$
--
--   From it we form the symmetric $3\times3$ matrix $\Gamma_f$ and the vector $\pi_f$:
--
--   $$
--   \Gamma_f(a,b)=\frac{T_f(\{a,b\})}{|H|\;m(\{a,b\})},\qquad \pi_f(a)=\frac{h_f(a)}{2|H|},
--   $$
--
--   where $h_f(a)$ is the number of vertices of colour $a$. Then for every colour $a$,
--
--   $$
--   \sum_{b\in\{0,1,2\}}\Gamma_f(a,b)=\pi_f(a).
--   $$
--
--   $\Gamma_f$ is the empirical joint distribution of the colours at the two ends of a standard pair, symmetrised over the two orientations, and $\pi_f$ is the empirical distribution of vertex colours. The identity says that $\pi_f$ is the marginal of $\Gamma_f$. When all $\pi_f(a)>0$, it shows that the normalised matrix $\Gamma_f(a,b)/\sqrt{\pi_f(a)\pi_f(b)}$ fixes the vector $(\sqrt{\pi_f(a)})_a$. When $H\ne\emptyset$, it shows that the colour histogram of $f$ is determined by its table.
--
--   **Formalization Note** No assumption $|H|>0$ is made. For empty $H$ both sides are $0$, because division by zero is $0$ in Lean. Types are encoded by a symmetric map from ordered colour pairs to $\{0,\dots,5\}$ (`threeEdgeType`), multiplicities by `typeMultiplicity`, the table by `threeTable`, and $\Gamma_f$, $\pi_f$ by `tableGamma f`, `tablePi f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean#L154-L170

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

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10
open Matrix
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem OAI.MatchingSmoothing.tableGamma_rowsum (f : H × Bool → Fin 3) (i : Fin 3) :
    ∑ j, tableGamma f i j = tablePi f i := by sorry
