-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_conditionalAverage_energy
-- name    : OAI.MatchingSmoothing.conditionalAverage_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:39:40.573877+00:00
-- url     : https://prove2.me/theorems/a9b77a94-0bf8-423f-978b-9f7891d54b28
-- title:
--   Energy of conditional averages equals the quadratic form of the normalised co-incidence operator
-- statement:
--   Let $X$ and $Z$ be nonempty finite sets and let $P\subseteq X\times Z$ be a relation; write $x\sim z$ when $(x,z)\in P$. Let $D\ne0$ be a real number and $f:X\to\mathbb R$. Define the *conditional average* of $f$ at $z\in Z$ by
--
--   $$
--   \bar f(z)=\frac{1}{E}\sum_{x\in X:\ x\sim z}f(x),\qquad E=\frac{|X|\,D}{|Z|},
--   $$
--
--   and the co-incidence operator $K_D$ on $\mathbb R^X$ by the matrix
--
--   $$
--   K_D(x,y)=\frac{1}{|X|}\cdot\frac{|Z|}{D^2}\,\#\{z\in Z:\ x\sim z\text{ and }y\sim z\}.
--   $$
--
--   Then
--
--   $$
--   \frac1{|Z|}\sum_{z\in Z}\bar f(z)^2\;=\;\frac1{|X|}\sum_{x\in X}f(x)\,(K_Df)(x).
--   $$
--
--   If every $x$ is related to exactly $D$ elements of $Z$, then $E$ is the average number of elements of $X$ related to a given $z$, and $\bar f(z)$ is an average of $f$ over the elements related to $z$. The identity expresses the mean square of these conditional averages as the quadratic form of $K_D$ with respect to the uniform probability measure on $X$. In particular this quadratic form is nonnegative, so $K_D$ is positive semidefinite. Upper bounds on the quadratic form of $K_D$ are therefore bounds on the mean square of the conditional averages.
--
--   **Formalization Note** $K_D$ is `incidenceOperator P D`, obtained from `incidenceKernel P D` by dividing by $|X|$, and $\bar f$ is `conditionalAverage P E f` with the stated value of $E$. The identity holds for every real $D\ne0$; no regularity of the relation is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/IncidenceKernels.lean#L149-L166

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

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6
open Matrix
variable {X : Type u_5} {Z : Type u_6} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

omit [DecidableEq X] [DecidableEq Z] in
theorem OAI.MatchingSmoothing.conditionalAverage_energy [Nonempty X] [Nonempty Z]
    (P : X → Z → Prop) (D : ℝ) (hD : D ≠ 0) (f : X → ℝ) :
    (∑ z, conditionalAverage P ((Fintype.card X : ℝ) * D / Fintype.card Z) f z ^ 2) /
      Fintype.card Z =
    (∑ x, f x * (incidenceOperator P D *ᵥ f) x) / Fintype.card X := by sorry
