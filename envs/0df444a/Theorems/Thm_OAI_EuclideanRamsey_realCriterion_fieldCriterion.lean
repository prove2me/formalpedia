-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_realCriterion_fieldCriterion
-- name    : OAI.EuclideanRamsey.realCriterion_fieldCriterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:36:20.961558+00:00
-- url     : https://prove2.me/theorems/6f2c5706-519d-47b8-8994-5804d33c62a6
-- title:
--   The real tensor criterion descends to the coordinate field
-- statement:
--   Let $s,d\in\mathbb{N}$ and let $a=(a_0,\dots,a_{s-1})$ be a family of points of $\mathbb{R}^d$, where $a_i$ has coordinates $a_{i1},\dots,a_{id}$. Let $K\subseteq\mathbb{R}$ be the *coordinate field* of $a$, the subfield generated over $\mathbb{Q}$ by all coordinates $a_{ij}$. Index rows and columns by the augmented set $\{\ast,1,\dots,d\}$ and let $\hat a_i$ be the augmented coordinate vector of $a_i$, that is $\hat a_i(\ast)=1$ and $\hat a_i(j)=a_{ij}$; all its entries lie in $K$. For a field $A\in\{K,\mathbb{R}\}$ write $m_A:A\otimes_{\mathbb{Q}}A\to A$, $u\otimes v\mapsto uv$, for the multiplication map.
--
--   Say that $a$ satisfies the *criterion over $A$* if there is a matrix $P=(P_{\alpha\beta})_{\alpha,\beta\in\{\ast,1,\dots,d\}}$ with entries in the commutative ring $A\otimes_{\mathbb{Q}}A$ such that
--
--   $$
--   \sum_{\alpha,\beta\in\{\ast,1,\dots,d\}}\bigl(\hat a_i(\alpha)\otimes1\bigr)\,P_{\alpha\beta}\,\bigl(1\otimes\hat a_i(\beta)\bigr)=0\quad(0\le i\le s-1),\qquad m_A(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d).
--   $$
--
--   The criterion over $\mathbb{R}$ is called the *real criterion* and the criterion over $K$ the *field criterion*.
--
--   **Theorem.** For all $s,d$ and every family $a$ as above, with no further hypotheses,
--
--   $$
--   a\ \text{satisfies the real criterion}\quad\Longrightarrow\quad a\ \text{satisfies the field criterion}.
--   $$
--
--   The reverse implication is immediate by base change along $K\subseteq\mathbb{R}$, so the two criteria are equivalent. The real form is the convenient one for analytic and geometric constructions of certificates (for instance by averaging over symmetries), while the field form is the hypothesis under which the Ramsey property of $a$ is established; this descent connects the two.
--
--   **Formalization Note** The field criterion is `FieldCriterion a`: $K$ is the intermediate field `coordinateField a`, the entries live in `TensorRing a` (that is $K\otimes_{\mathbb{Q}}K$), $\hat a_i$ is `augmented a i` and $m_K$ is `multiply a`. The real criterion is `RealCriterion a`, phrased with the $\mathbb{Q}$-linear maps `arrayEvaluation a i` (the left-hand sums) and `spatialMultiply` (the block $(m_{\mathbb{R}}(P_{\alpha\beta}))_{1\le\alpha,\beta\le d}$, required to be the identity matrix). The augmented index set is `Option (Fin d)`, with `none` in the role of $\ast$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorDescent.lean#L94-L119

import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive

open OAI OAI.EuclideanRamsey
universe uIndex
open scoped TensorProduct RealInnerProductSpace

theorem OAI.EuclideanRamsey.realCriterion_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : RealCriterion a) : FieldCriterion a := by sorry
