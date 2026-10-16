-- Prove2me | Theorems.Thm_OAI_CrossEnsemble_shifted_left_operator_eq
-- name    : OAI.CrossEnsemble.shifted_left_operator_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:18:49.228108+00:00
-- url     : https://prove2.me/theorems/3b8d4c88-1822-4ce5-a3d2-e76ecc50b712
-- title:
--   Equal ensemble operators stay equal after a common coordinate shift of the left factors
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$; inner products are conjugate-linear in the first argument. For families $u=(u_i)_{i\in I}$, $v=(v_i)_{i\in I}$ in $\mathcal F_n$ with $\sum_i\|u_i\|^2,\sum_i\|v_i\|^2<\infty$, let $\Omega(u,v)=\sum_i|u_i\rangle\langle v_i|$ be the bounded operator $w\mapsto\sum_i\langle v_i,w\rangle\,u_i$.
--
--   Let $x,y:I\to\mathcal F_n$ and $u,v:J\to\mathcal F_n$ be square-summable families over arbitrary index sets $I,J$. Let $f:\mathbb{N}^n\to\mathbb{N}^n$ be any map and $c:\mathbb{N}^n\to\mathbb{C}$ any function such that
--   $$
--   y_i(k)=c(k)\,x_i(f(k))\quad\text{and}\quad v_m(k)=c(k)\,u_m(f(k))\qquad\text{for all }i\in I,\ m\in J,\ k\in\mathbb{N}^n .
--   $$
--
--   **Theorem.** If $\Omega(x,x)=\Omega(u,u)$, then
--   $$
--   \Omega(y,x)=\Omega(v,u).
--   $$
--
--   The operator $\Omega(x,x)$ is the (unnormalized) density operator of the ensemble $x$. The statement says that the cross operator obtained by transforming the left-hand (ket) vectors with a fixed weighted substitution of coordinates, such as a raising operator in the number basis, depends only on that density operator and not on the decomposition. It is the companion of the analogous statement for the right factors.
--
--   **Formalization Note** $\Omega$ is `CrossEnsemble.operator`; square-summability of $y$ and $v$ is assumed separately, and $f$ need not be injective.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L1065-L1087

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace

open OAI OAI.CrossEnsemble
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

theorem OAI.CrossEnsemble.shifted_left_operator_eq (x y : I → Fock n) (u v : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (f : NumberIndex n → NumberIndex n) (c : NumberIndex n → ℂ)
    (hyx : ∀ i k, y i k=c k*x i (f k)) (hvu : ∀ j k, v j k=c k*u j (f k))
    (he : operator x x=operator u u) : operator y x=operator v u := by sorry
