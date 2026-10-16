-- Prove2me | Theorems.Thm_OAI_BeamLadder_tensorPreimage_lowerR
-- name    : OAI.BeamLadder.tensorPreimage_lowerR
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:16:39.765142+00:00
-- url     : https://prove2.me/theorems/fb046ea4-5196-43de-bdbe-5a5329ba4633
-- title:
--   Weighted second-port lowering of the tensor preimage vector
-- statement:
--   On the two-port space $\mathcal F_n^{(2)}=\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$, with number basis $|k,e\rangle$, put $W(k,e)=\nu(k)+\nu(e)-1=1+|k|+|e|$, where $\nu(k)=1+\sum_j k_j$ (so $W\ge 1$ is one plus the total photon number of both ports), and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$. For $m\in\mathbb{N}$ let $\nu^{-m}$ be the diagonal operator $(\nu^{-m}y)(k)=\nu(k)^{-m}y(k)$ on $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$, and for $y,z\in\mathcal F_n$ let $y\otimes z\in\mathcal F_n^{(2)}$ be $(y\otimes z)(k,e)=y(k)\,z(e)$. The tensor preimage of $x,y\in\mathcal F_n$ is
--   $$
--   T(x,y)=\nu^{-2}x\otimes\nu^{-3}y+\nu^{-3}x\otimes\nu^{-2}y-\nu^{-3}x\otimes\nu^{-3}y ,
--   $$
--   which in coordinates is $T(x,y)(k,e)=W(k,e)\,(\nu^{-3}x)(k)\,(\nu^{-3}y)(e)$, i.e. a vector whose image under $W^{-1}$ is $\nu^{-3}x\otimes\nu^{-3}y$.
--
--   The weighted lowering operator of mode $j$ on the second port is $(R_jw)(k,e)=\frac{\sqrt{e_j+1}}{W(k,e)+1}\,w(k,e+e_j)$, and on $\mathcal F_n$ let $\Lambda_j$ be the bounded operator $(\Lambda_jy)(k)=\sqrt{k_j+1}\,\nu(k+e_j)^{-3}\,y(k+e_j)$ (formally $a_j\nu^{-3}$).
--
--   **Theorem.** For every mode $j$ and all $x,y\in\mathcal F_n$,
--   $$
--   R_j\,T(x,y)=\nu^{-3}x\otimes\Lambda_jy .
--   $$
--
--   Thus the two-port ladder operator, applied to a vector of the form $W\,(\nu^{-3}x\otimes\nu^{-3}y)$, acts only on the corresponding tensor factor, where it becomes the one-port weighted ladder operator. This is how two-port weak forms of the thermal generator are reduced to one-port expressions for product inputs.
--
--   **Formalization Note** $T(x,y)$ is `BeamLadder.tensorPreimage x y`, $\nu^{-m}$ is `inverseWeight m`, $\otimes$ is `TensorLp.tensor`; $R_j$ is `BeamLadder.lowerR j`, $\Lambda_j$ is `Annihilation.sandwich 0 3 _ j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L628-L640

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace

open OAI OAI.BeamLadder
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem OAI.BeamLadder.tensorPreimage_lowerR (j : Fin n) (x y : Fock n) :
    lowerR j (tensorPreimage x y)=tensor (inverseWeight 3 x) (sandwich 0 3 (by omega) j y) := by sorry
