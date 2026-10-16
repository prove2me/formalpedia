-- Prove2me | Theorems.Thm_OAI_BeamLadder_tensorPreimage2_summable
-- name    : OAI.BeamLadder.tensorPreimage2_summable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:35:18.430976+00:00
-- url     : https://prove2.me/theorems/a6107d0e-6534-4ec1-8634-0749e3081479
-- title:
--   Square-summability of the product family of second tensor preimages
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$, let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m}x(k)$ (formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$), and for a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index; $k - \mathbf 1_j$ lowers the $j$-th entry by one, truncated at $0$. Write $|u\rangle\langle v|$ for the rank-one operator $y \mapsto \langle v, y\rangle\,u$, and $T_{kl} = \langle e_k, T e_l\rangle$ for number-basis matrix entries.
--
--   On the two-port space $\mathcal J_n = \ell^2(\mathbb{N}^n \times \mathbb{N}^n)$ write $(u \otimes v)(k,m) = u(k)\,v(m)$ for $u, v \in \mathcal F_n$, and $W(k,m) = w(k) + w(m) - 1 = 1 + |k| + |m|$. For $x, y \in \mathcal F_n$ define the *second tensor preimage*
--   $$
--   T(x,y) = \Lambda x \otimes \Lambda^3 y + \Lambda^3 x\otimes \Lambda y + \Lambda^3x\otimes\Lambda^3y + 2\,\Lambda^2x\otimes\Lambda^2y - 2\,\Lambda^2x\otimes\Lambda^3y - 2\,\Lambda^3x\otimes\Lambda^2y \ \in \mathcal J_n .
--   $$
--
--   **Theorem.** Let $(x_i)_{i\in I}$ and $(y_l)_{l \in L}$ be families in $\mathcal F_n$ with $\sum_i \|x_i\|^2 < \infty$ and $\sum_l \|y_l\|^2 < \infty$. Then
--   $$
--   \sum_{(i,l) \in I \times L} \big\|T(x_i, y_l)\big\|^2 < \infty .
--   $$
--
--   Coefficientwise $T(x,y)(k,m) = W(k,m)^2\,w(k)^{-3}w(m)^{-3}\,x(k)\,y(m)$, because $a^2 + b^2 + 1 + 2ab - 2a - 2b = (a+b-1)^2$; so $T(x,y)$ is a preimage of $\Lambda^3x\otimes\Lambda^3y$ under multiplication by $W^{-2}$. The lemma makes the product family $(T(x_i,y_l))$ an admissible square-summable ensemble on the two-port space, so that trace pairings against it converge.
--
--   **Formalization Note** $T$ is `BeamLadder.tensorPreimage2`, $\otimes$ is `TensorLp.tensor`, $\Lambda^m$ is `inverseWeight m`, and summability is `Summable` over the product type `I × J`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean#L550-L563

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms

open OAI OAI.BeamLadder
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
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem OAI.BeamLadder.tensorPreimage2_summable {I J : Type*} (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensorPreimage2 (x ij.1) (y ij.2)‖^2) := by sorry
