-- Prove2me | Theorems.Thm_OAI_TensorLp_liftLeft_positive
-- name    : OAI.TensorLp.liftLeft_positive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:06:45.46855+00:00
-- url     : https://prove2.me/theorems/d2362a8d-c6d6-4b0f-a016-88628096b118
-- title:
--   Tensoring a positive operator with the identity keeps it positive on $\ell^2(A\times B)$
-- statement:
--   Let $A$ and $B$ be arbitrary index sets and write $\ell^2(A)=\ell^2(A;\mathbb{C})$. A vector $z\in\ell^2(A\times B)$ has slices $z_b\in\ell^2(A)$, $z_b(a)=z(a,b)$, for $b\in B$. For a bounded operator $Z$ on $\ell^2(A)$, its lift $Z\otimes 1_B$ is the bounded operator on $\ell^2(A\times B)$ acting slice by slice:
--   $$
--   \bigl((Z\otimes 1_B)z\bigr)(a,b)=(Z z_b)(a).
--   $$
--
--   **Theorem.** If $Z$ is positive, i.e. symmetric with $\operatorname{Re}\langle Zy,y\rangle\ge 0$ for all $y\in\ell^2(A)$, then $Z\otimes 1_B$ is positive:
--   $$
--   Z\ge 0\quad\Longrightarrow\quad Z\otimes 1_B\ge 0 .
--   $$
--
--   This is the basic fact that an observable acting on one tensor factor remains positive when the other factor is added; it lets positivity of one-port operators be transported to the two-port space on which beam-splitter computations take place.
--
--   **Formalization Note** The lift is `TensorLp.liftLeft (B := B) Z` and positivity is Mathlib's `ContinuousLinearMap.IsPositive` (symmetric and nonnegative real part of $\langle Tx,x\rangle$). No countability is assumed on $A$ or $B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TensorLp.lean#L221-L233

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp

open OAI OAI.TensorLp
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
variable {A B : Type*}

theorem OAI.TensorLp.liftLeft_positive {Z : H A →L[ℂ] H A} (hZ : Z.IsPositive) :
    (liftLeft (B := B) Z).IsPositive := by sorry
