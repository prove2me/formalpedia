-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_predicateAverage_of_constant
-- name    : OAI.MatchingSmoothing.predicateAverage_of_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:53:57.037742+00:00
-- url     : https://prove2.me/theorems/03cba52a-8fee-42d0-84e1-85d544b5b8c6
-- title:
--   The average of a function over a nonempty set on which it is constant equals that constant
-- statement:
--   Let $X$ be a finite set, let $A\subseteq X$ be a subset (given by a predicate on $X$), and let $f:X\to\mathbb R$. The average of $f$ over $A$ is
--
--   $$
--   \operatorname{Avg}_Af=\frac{1}{|A|}\sum_{x\in A}f(x).
--   $$
--
--   If $A$ is nonempty and $f(x)=c$ for every $x\in A$, where $c\in\mathbb R$, then
--
--   $$
--   \operatorname{Avg}_Af=c .
--   $$
--
--   This elementary fact is used to evaluate the average of a symmetrized function over a color-table class of perfect matchings, on which the symmetrized function is constant.
--
--   **Formalization Note** The average is `predicateAverage P`, the linear functional $f\mapsto|A|^{-1}\sum_{x\in X}\mathbf 1[P(x)]f(x)$. With Lean's convention $0^{-1}=0$ the average over an empty set would be $0$, which is why the hypothesis that some $x$ satisfies $P$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TablePolynomials.lean#L38-L52

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
variable {X : Type u_1} [Fintype X]

theorem OAI.MatchingSmoothing.predicateAverage_of_constant (P : X → Prop) (c : ℝ) (hP : ∃ x, P x)
    (f : X → ℝ) (hf : ∀ x, P x → f x = c) : predicateAverage P f = c := by sorry
