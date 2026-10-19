-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_table_average_polynomial
-- name    : OAI.MatchingSmoothing.table_average_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:54:55.5492+00:00
-- url     : https://prove2.me/theorems/c9a33036-183c-492a-854c-791388b548ef
-- title:
--   Averages of low-degree matching polynomials over color-table classes are polynomials in the bichromatic edge counts
-- statement:
--   Let $H$ be a finite set and $V=H\times\{0,1\}$. Represent the perfect matchings of $V$ as fixed-point-free involutions $M$ of $V$, write $x_{(u,w)}(M)=1$ if $M(u)=w$ and $0$ otherwise, and let $\mathcal P_d$ be the span of all products of at most $d$ such edge indicators (including the constant $1$). Fix a coloring $z:V\to\{0,1,2\}$. The color table $\operatorname{tab}_z(M)=(t_{\{a,b\}})$ of a matching $M$ records, for each of the six unordered color pairs $\{a,b\}$ ($a=b$ allowed), the number of edges of $M$ whose endpoints have colors $a$ and $b$. For a vector $t$ of six natural numbers let $\mathcal M_t$ be the set of perfect matchings $M$ with $\operatorname{tab}_z(M)=t$.
--
--   Let $d\in\mathbb N$ and $f\in\mathcal P_d$. Then there is a real polynomial $P$ in three variables, of total degree at most $d$, such that for every $t$ that is the table of some matching (i.e. $\mathcal M_t\neq\emptyset$),
--
--   $$
--   \frac{1}{|\mathcal M_t|}\sum_{M\in\mathcal M_t}f(M)\;=\;P\big(t_{\{0,1\}},\,t_{\{0,2\}},\,t_{\{1,2\}}\big).
--   $$
--
--   The polynomial $P$ depends on $z$, $d$ and $f$ but not on $t$. Thus the class average of a low-degree function of perfect matchings depends only on the three bichromatic edge counts, and polynomially so with the same degree bound. Together with smoothing estimates for the high-degree part, this shows that class averages of arbitrary bounded functions are close to low-degree polynomials of the table.
--
--   **Formalization Note** $P$ is an element of `lowDegree (fun i (v : Fin 3 → ℝ) => v i) d`, evaluated at `fun i => t (threeEdgeType (crossPair i))`. Here `crossPair` lists the pairs (0,1), (0,2), (1,2), and `threeEdgeType` numbers the unordered pairs {0,0}, {0,1}, {0,2}, {1,1}, {1,2}, {2,2} as 0, ..., 5. The average is `predicateAverage (fun M => M.table z = t) f`, and the table is `Pairing.table`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TablePolynomials.lean#L80-L100

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4
attribute [local instance] Classical.propDecidable
variable {H : Type u_4} [Fintype H] [DecidableEq H]

theorem OAI.MatchingSmoothing.table_average_polynomial (z : H × Bool → Fin 3) (d : ℕ)
    (f : Pairing (H × Bool) → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    ∃ P ∈ lowDegree (fun i (v : Fin 3 → ℝ) => v i) d,
      ∀ t : Fin 6 → ℕ, (∃ M : Pairing (H × Bool), M.table z = t) →
        predicateAverage (fun M => M.table z = t) f =
          P (fun i => (t (threeEdgeType (crossPair i)) : ℝ)) := by sorry
