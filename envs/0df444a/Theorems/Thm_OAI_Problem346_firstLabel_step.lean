-- Prove2me | Theorems.Thm_OAI_Problem346_firstLabel_step
-- name    : OAI.Problem346.firstLabel_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:41:39.911956+00:00
-- url     : https://prove2.me/theorems/99720fc6-5c28-4b4d-8422-3b2b704f5fae
-- title:
--   Consecutive labellings of the first transfer differ in exactly one slot
-- statement:
--   Fix $r,m\in\mathbb{N}$. Consider a grid of *slots* $(i,j)$ with rows $i\in\{0,\dots,r\}$ and columns $j\in\{0,\dots,r+m-1\}$, and the alphabet of *block labels* $x,\ t,\ y_0,\dots,y_{m-1}$. For $k\in\mathbb{N}$ the labelling $\lambda_k$ of the grid is defined by
--
--   $$\lambda_k(0,j)=\begin{cases}y_j, & j<k\ \text{and}\ j<m,\\ t, & \text{otherwise},\end{cases}\qquad \lambda_k(i,j)=\begin{cases}x, & j<r,\\ y_{j-r}, & j\ge r,\end{cases}\quad(1\le i\le r).$$
--
--   So row $0$ carries $y_0,\dots,y_{k-1}$ followed by copies of $t$, while each of the rows $1,\dots,r$ carries $r$ copies of $x$ followed by $y_0,\dots,y_{m-1}$, independently of $k$.
--
--   **Theorem.** For every $k<m$, the labelling $\lambda_{k+1}$ is obtained from $\lambda_k$ by relabelling the single slot $(0,k)$ with $y_k$:
--
--   $$\lambda_{k+1}=\lambda_k\big[(0,k)\mapsto y_k\big],$$
--
--   that is, $\lambda_{k+1}(0,k)=y_k$ and $\lambda_{k+1}(i,j)=\lambda_k(i,j)$ for every other slot $(i,j)$.
--
--   Reading each row as a product of vector variables, $\lambda_0$ describes the row products $t^{r+m}$ and ($r$ times) $x^ry_0\cdots y_{m-1}$, and $\lambda_m$ replaces the first row by $y_0\cdots y_{m-1}t^r$. The theorem says that the passage from $\lambda_0$ to $\lambda_m$ consists of $m$ single-slot moves $t\to y_k$; each of them is realized by one directional derivative of the associated coordinate polynomial.
--
--   **Formalization Note** $\lambda_k$ is `firstLabel r m k`, a function on `Fin (r+1) × Fin (r+m)` with values in `FirstBlock m = Option (Option (Fin m))`, where `none` is $x$, `some none` is $t$ and `some (some j)` is $y_j$. The column $k$ is regarded as an element of `Fin (r+m)` using $k<m\le r+m$, and the relabelling is `Function.update`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FirstCounts.lean#L100-L122

import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts

open OAI OAI.Problem346
open scoped BigOperators

theorem OAI.Problem346.firstLabel_step (r m k : ℕ) (hk : k < m) :
    firstLabel r m (k + 1) = Function.update (firstLabel r m k)
      (0, ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩) (some (some ⟨k, hk⟩)) := by sorry
