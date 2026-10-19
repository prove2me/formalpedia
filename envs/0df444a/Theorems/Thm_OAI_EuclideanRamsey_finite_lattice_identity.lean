-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_finite_lattice_identity
-- name    : OAI.EuclideanRamsey.finite_lattice_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:13:55.970826+00:00
-- url     : https://prove2.me/theorems/e1cc9e05-5071-41e6-8cb6-022415c01137
-- title:
--   Finite lattice identity: a rational measure on $\mathbb Z^k$ with vanishing coset sums and prescribed second moments
-- statement:
--   Let $k\ge1$ and $s\ge1$. Write $\mathbb Q[\mathbb Z^k]$ for the rational group algebra of $\mathbb Z^k$ (finitely supported functions $\nu:\mathbb Z^k\to\mathbb Q$ with convolution product), and for $\nu\in\mathbb Q[\mathbb Z^k]$ write
--   $$m(\nu)=\sum_{\gamma}\nu(\gamma),\qquad m_a(\nu)=\sum_{\gamma}\nu(\gamma)\,\gamma_a,\qquad m_{ab}(\nu)=\sum_{\gamma}\nu(\gamma)\,\gamma_a\gamma_b\qquad(1\le a,b\le k)$$
--   for its mass, first moments and second moments. For a subgroup $\Lambda\le\mathbb Z^k$ let $\pi_\Lambda\nu:\mathbb Z^k/\Lambda\to\mathbb Q$, $\pi_\Lambda\nu(\gamma+\Lambda)=\sum_{\delta\in\gamma+\Lambda}\nu(\delta)$, be the coset pushforward, and let $L_\Lambda\subseteq\mathbb Q^k$ be the $\mathbb Q$-linear span of $\Lambda$. For a rational $k\times k$ matrix $C$ put $\widehat C=\sum_{a,b=1}^kC_{ab}\,e_a\otimes e_b\in\mathbb Q^k\otimes_{\mathbb Q}\mathbb Q^k$.
--
--   **Theorem.** Let $\Lambda_1,\dots,\Lambda_s$ be subgroups of $\mathbb Z^k$ and let $C$ be a symmetric rational $k\times k$ matrix such that, for every $i$, the image of $\widehat C$ in $(\mathbb Q^k/L_{\Lambda_i})\otimes_{\mathbb Q}(\mathbb Q^k/L_{\Lambda_i})$ is zero. Then there exists $\nu\in\mathbb Q[\mathbb Z^k]$ with
--   $$\pi_{\Lambda_i}\nu=0\ \ (1\le i\le s),\qquad m(\nu)=0,\qquad m_a(\nu)=0,\qquad m_{ab}(\nu)=C_{ab}\ \ (1\le a,b\le k).$$
--
--   Equivalently, the hypothesis says $\widehat C\in L_{\Lambda_i}\otimes\mathbb Q^k+\mathbb Q^k\otimes L_{\Lambda_i}$ for each $i$. The theorem turns this linear-algebraic condition into a concrete finite signed rational measure on $\mathbb Z^k$ that is invisible on every coset space $\mathbb Z^k/\Lambda_i$, has vanishing mass and first moments, and has second-moment matrix exactly $C$. In the classification of Ramsey configurations this lattice stencil is the object that is subsequently smoothed and converted into geometry.
--
--   **Formalization Note** The statement is the proposition `FiniteLatticeIdentity`. Here $\mathbb Q[\mathbb Z^k]$ is `LatticeRing k`, $\widehat C$ is `matrixTensor C`, $L_\Lambda$ is `latticeSpan Λ`, the quotient condition is `quotientTensor (Λ i) (matrixTensor C) = 0`, and $m,m_a,m_{ab},\pi_\Lambda$ are `mass`, `firstMoment`, `secondMoment`, `cosetPushforward`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean#L422-L442

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting

open OAI OAI.EuclideanRamsey
universe uRing uGroup uSemigroup uModule uModuleTarget uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct
variable {k : ℕ}

theorem OAI.EuclideanRamsey.finite_lattice_identity : FiniteLatticeIdentity := by sorry
