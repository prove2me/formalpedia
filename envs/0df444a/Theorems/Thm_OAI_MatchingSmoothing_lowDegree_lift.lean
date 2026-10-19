-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_lowDegree_lift
-- name    : OAI.MatchingSmoothing.lowDegree_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:53:09.165201+00:00
-- url     : https://prove2.me/theorems/5b238dc8-eee6-4a63-86f0-2a932bbea628
-- title:
--   A function of low degree in given coordinate functions is a low-degree polynomial of those coordinates
-- statement:
--   Let $X$ and $E$ be sets and let $(x_e)_{e\in E}$ be a family of real-valued functions on $X$. For $d\in\mathbb N$ let $\mathcal P_d(x)$ be the real linear span of all products $x_{e_1}x_{e_2}\cdots x_{e_m}$ with $m\le d$ and $e_1,\dots,e_m\in E$ (repetitions allowed; the empty product is the constant $1$). Apply the same construction to the space $\mathbb R^E$ of all functions $v:E\to\mathbb R$ with the coordinate functions $\pi_e(v)=v(e)$: then $\mathcal P_d(\pi)$ is the space of real polynomial functions on $\mathbb R^E$ of total degree at most $d$ (each involving finitely many coordinates).
--
--   If $f\in\mathcal P_d(x)$, then there is $P\in\mathcal P_d(\pi)$ such that
--
--   $$
--   f(\alpha)=P\big((x_e(\alpha))_{e\in E}\big)\qquad\text{for every }\alpha\in X .
--   $$
--
--   So a function that is a polynomial of degree at most $d$ in the functions $x_e$ factors through the feature map $\alpha\mapsto(x_e(\alpha))_{e\in E}$ via an honest polynomial of the same degree. It is used with three coordinate functions (the bichromatic edge counts of a 3-colored matching) to produce a polynomial in three real variables.
--
--   **Formalization Note** $\mathcal P_d(x)$ is `lowDegree x d` and $\mathcal P_d(\pi)$ is `lowDegree (fun e (v : E → ℝ) => v e) d`. The section also declares type variables `I` and `Y` that do not occur in this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/ColorPolynomials.lean#L113-L135

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

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6
attribute [local instance] Classical.propDecidable
variable {E : Type u_3} {I : Type u_4} {X : Type u_5} {Y : Type u_6}

theorem OAI.MatchingSmoothing.lowDegree_lift (x : E → X → ℝ) (d : ℕ) (f : X → ℝ)
    (hf : f ∈ lowDegree x d) :
    ∃ P ∈ lowDegree (fun e (v : E → ℝ) => v e) d,
      ∀ a, f a = P (fun e => x e a) := by sorry
