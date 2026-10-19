-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_TransitiveConsequence_averaged_realCriterion
-- name    : OAI.EuclideanRamsey.TransitiveConsequence.averaged_realCriterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:44:34.003639+00:00
-- url     : https://prove2.me/theorems/be5ffe90-ec40-4379-b812-31b33ae0229c
-- title:
--   Configurations congruent to part of a finite transitive configuration satisfy the real tensor criterion
-- statement:
--   Let $s\ge1$ and $d,t,D\ge0$ be integers, and consider the following data.
--
--   1. Points $a_0,\dots,a_{s-1}\in\mathbb{R}^d$, where $a_i$ has coordinates $a_{i1},\dots,a_{id}$, whose affine span is all of $\mathbb{R}^d$.
--   2. Points $y_0,\dots,y_{t-1}\in\mathbb{R}^D$. Let $G(y)$ be the group of permutations $\sigma$ of $\{0,\dots,t-1\}$ preserving all mutual distances, $\|y_{\sigma(k)}-y_{\sigma(l)}\|=\|y_k-y_l\|$ for all $k,l$. Assume that $y$ is *transitive*: for all $k,l$ there is $\sigma\in G(y)$ with $\sigma(k)=l$.
--   3. A map $e:\{0,\dots,s-1\}\to\{0,\dots,t-1\}$ such that $\|y_{e(i)}-y_{e(j)}\|=\|a_i-a_j\|$ for all $i,j$.
--
--   Write $\hat a_i$ for the augmented coordinate vector of $a_i$, indexed by $\{\ast,1,\dots,d\}$ with $\hat a_i(\ast)=1$ and $\hat a_i(j)=a_{ij}$, and $m:\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}\to\mathbb{R}$, $u\otimes v\mapsto uv$, for the multiplication map. Then $a$ satisfies the *real criterion*: there is a matrix $(P_{\alpha\beta})_{\alpha,\beta\in\{\ast,1,\dots,d\}}$ with entries in $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$ such that
--
--   $$
--   \sum_{\alpha,\beta\in\{\ast,1,\dots,d\}}\bigl(\hat a_i(\alpha)\otimes1\bigr)P_{\alpha\beta}\bigl(1\otimes\hat a_i(\beta)\bigr)=0\quad(0\le i\le s-1),\qquad m(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d).
--   $$
--
--   No injectivity of $a$, $y$ or $e$ is assumed. Together with the descent of the real criterion to the coordinate field and the sufficiency of the field criterion for the Ramsey property, this is the algebraic input in showing that configurations congruent to subsets of finite transitive configurations are Ramsey.
--
--   **Formalization Note** The group $G(y)$ is `distancePermutationGroup y`, a subgroup of `Equiv.Perm (Fin t)`; transitivity is `IsTransitive y`; the congruence hypothesis is `Congruent a (fun i => y (e i))`; the affine-span hypothesis is `affineSpan ℝ (Set.range a) = ⊤`; and the conclusion is `RealCriterion a`, whose two conditions are `arrayEvaluation a i P = 0` for all `i` and `spatialMultiply P = 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Transitive.lean#L48-L115

import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Transitive

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.TransitiveConsequence
open scoped TensorProduct BigOperators

theorem OAI.EuclideanRamsey.TransitiveConsequence.averaged_realCriterion {s d t D : ℕ}
    (a : Fin s → Space d) (hs : 0 < s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (y : Fin t → Space D) (hy : IsTransitive y)
    (e : Fin s → Fin t) (he : Congruent a (fun i => y (e i))) :
    RealCriterion a := by sorry
