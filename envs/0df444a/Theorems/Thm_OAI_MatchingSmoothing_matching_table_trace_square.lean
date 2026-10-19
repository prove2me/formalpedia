-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_matching_table_trace_square
-- name    : OAI.MatchingSmoothing.matching_table_trace_square
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:42:10.126992+00:00
-- url     : https://prove2.me/theorems/03c6d6d7-3a65-45b6-8ded-6264db872bc7
-- title:
--   Trace bound for the square of the matching–colouring table incidence operator
-- statement:
--   Let $H$ be a nonempty finite set and $V=H\times\{0,1\}$, and let $\mathcal P$ be the set of perfect matchings of $V$, viewed as fixed-point-free involutions. For a $3$-colouring $f:V\to\{0,1,2\}$ and each of the six unordered colour pairs $t$:
--
--   * $h_f(a)$ is the number of vertices of colour $a$;
--   * $T_f(t)$ is the number of standard pairs $\{(i,0),(i,1)\}$ whose unordered colour pair is $t$;
--   * for a matching $M$, $\mathrm{tab}_M(f)(t)$ is the number of edges of $M$ whose unordered pair of endpoint colours is $t$.
--
--   Fix a reference colouring $f_0$ using every colour ($h_{f_0}(a)>0$ for $a=0,1,2$). Let $\mathcal Z=\{z:V\to\{0,1,2\}:\ h_z=h_{f_0}\}$ be the set of colourings with the colour counts of $f_0$. Relate $M\in\mathcal P$ to $z\in\mathcal Z$ when $\mathrm{tab}_M(z)=T_{f_0}$, i.e. when $M$ looks under $z$ exactly as the standard matching looks under $f_0$. With $D=\#\{f:V\to\{0,1,2\}:\ T_f=T_{f_0}\}$, define the operator $K$ on $\mathbb R^{\mathcal P}$ by
--
--   $$
--   K(M,N)=\frac1{|\mathcal P|}\cdot\frac{|\mathcal Z|}{D^2}\,\#\{z\in\mathcal Z:\ \mathrm{tab}_M(z)=\mathrm{tab}_N(z)=T_{f_0}\}.
--   $$
--
--   Then
--
--   $$
--   \operatorname{tr}\big(K^2\big)\ \le\ (|H|+1)^{33}.
--   $$
--
--   $D$ is the number of colourings in $\mathcal Z$ related to the standard matching, and by symmetry to every matching. So $K$ is the normalised co-incidence operator of this relation. For a function $F$ on $\mathcal P$, its quadratic form with respect to the uniform measure on $\mathcal P$ equals the mean square over $z\in\mathcal Z$ of the suitably normalised sums of $F$ over the matchings related to $z$. The theorem bounds the squared Hilbert–Schmidt norm of $K$ polynomially in $|H|$, although the number of matchings grows superexponentially. A bound of this form is exactly the trace input of the multiplicity-based eigenvalue estimate, in which large eigenvalue multiplicities and a small $\operatorname{tr}(B^2)$ together bound the quadratic form of $B$.
--
--   **Formalization Note** $K$ is `incidenceOperator (tableRelation f₀) D` and $\mathcal Z$ is `Colorings (H × Bool) (Fin 3) (histogram f₀)`. The matching table $\mathrm{tab}_M$ is `Pairing.table`, defined by halving a vertex count with natural-number division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatchingIncidence.lean#L119-L144

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

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3
variable {H : Type u_3} [Fintype H] [DecidableEq H]

theorem OAI.MatchingSmoothing.matching_table_trace_square (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
    Matrix.trace (incidenceOperator (tableRelation f₀) D *
      incidenceOperator (tableRelation f₀) D) ≤ (Fintype.card H + 1 : ℝ) ^ 33 := by sorry
