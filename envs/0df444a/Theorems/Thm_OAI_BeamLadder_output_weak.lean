-- Prove2me | Theorems.Thm_OAI_BeamLadder_output_weak
-- name    : OAI.BeamLadder.output_weak
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:19:40.285309+00:00
-- url     : https://prove2.me/theorems/b7fa47c7-c5be-45d3-905b-195c30cd044b
-- title:
--   Weak form of the retained-port thermal generator through a reduced one-port ensemble
-- statement:
--   On the two-port space $\mathcal F_n^{(2)}=\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$, with number basis $|k,e\rangle$, put $W(k,e)=\nu(k)+\nu(e)-1=1+|k|+|e|$, where $\nu(k)=1+\sum_j k_j$ (so $W\ge 1$ is one plus the total photon number of both ports), and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$. Let $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$, with $\nu^{-m}$ the diagonal operator $(\nu^{-m}y)(k)=\nu(k)^{-m}y(k)$, and let $W^{-1}$ be the diagonal operator $(W^{-1}w)(k,e)=W(k,e)^{-1}w(k,e)$ on $\mathcal F_n^{(2)}$. For $w\in\mathcal F_n^{(2)}$ and $e\in\mathbb{N}^n$ the slice $w_e\in\mathcal F_n$ is $w_e(k)=w(k,e)$. Inner products are conjugate-linear in the first argument.
--
--   Two-port operators: $(L_jw)(k,e)=\frac{\sqrt{k_j+1}}{W(k,e)+1}w(k+e_j,e)$ is the weighted lowering operator of mode $j$ on the first port, and $\tilde L_j=h(W)L_j^*$ with $h(w)=\frac{w}{w-1}$ for $w>1$, $h(w)=0$ otherwise, is the corresponding weighted raising operator. One-port operators: $(\Lambda_jy)(k)=\sqrt{k_j+1}\,\nu(k+e_j)^{-3}y(k+e_j)$ and $\Lambda_j^\dagger$ with $(\Lambda_j^\dagger y)(k+e_j)=\sqrt{k_j+1}\,\nu(k)^{-3}y(k)$, $(\Lambda_j^\dagger y)(k)=0$ if $k_j=0$. For families $u,v$ write $\Omega(u,v)=\sum_i|u_i\rangle\langle v_i|$. For a bounded $Z$ on $\mathcal F_n$, $Z\otimes1$ acts on $\mathcal F_n^{(2)}$ slice by slice, $((Z\otimes1)w)_e=Zw_e$.
--
--   For $r\in\mathbb{R}$, a mode $j$, vectors $w,w'\in\mathcal F_n^{(2)}$ and a bounded $T$ on $\mathcal F_n^{(2)}$ put
--   $$
--   \mathcal W_{r,j}(w,w';T)=(r+1)\,\langle L_jw,\,T\,W^{-1}w'\rangle-r\,\langle W^{-1}w,\,T\,\tilde L_jw'\rangle,
--   $$
--   and for a family $z$ in $\mathcal F_n$ and bounded $Z$ on $\mathcal F_n$
--   $$
--   \mathcal S_{r,j}(z;Z)=(r+1)\sum_m\langle \Lambda_jz_m,\,Z\,\nu^{-3}z_m\rangle-r\sum_m\langle\nu^{-3}z_m,\,Z\,\Lambda_j^\dagger z_m\rangle .
--   $$
--
--   **Theorem.** Let $x=(x_i)_{i\in I}$ in $\mathcal F_n^{(2)}$ and $z=(z_m)_{m\in J}$ in $\mathcal F_n$ be square-summable families such that
--   $$
--   \Omega(s,s)=\Omega(\nu^{-3}z,\nu^{-3}z),\qquad s=\bigl((W^{-1}x_i)_e\bigr)_{(i,e)\in I\times\mathbb{N}^n},
--   $$
--   i.e. the partial trace over the second port of $\sum_i|W^{-1}x_i\rangle\langle W^{-1}x_i|$ equals $\sum_m|\nu^{-3}z_m\rangle\langle\nu^{-3}z_m|$. Then for every $r\in\mathbb{R}$, every mode $j$ and every bounded $Z$ on $\mathcal F_n$,
--   $$
--   \sum_{i\in I}\mathcal W_{r,j}(x_i,x_i;Z\otimes1)=\mathcal S_{r,j}(z;Z).
--   $$
--
--   The left side is the weak (tested) form of the retained-port part of the weighted thermal generator acting on a two-port ensemble, tested against an observable of the retained port only; the theorem shows that it depends only on the reduced one-port ensemble $z$ and equals the corresponding one-port expression.
--
--   **Formalization Note** $\mathcal W_{r,j}$ is `BeamLadder.weakL`, $\mathcal S_{r,j}$ is `BeamLadder.singleWeak`, $W^{-1}$ is `BeamLadder.inverse`, $\tilde L_j$ is `raiseL`, $\Lambda_j$ and $\Lambda_j^\dagger$ are `sandwich 0 3` and `creationSandwich 0 3`, $Z\otimes1$ is `TensorLp.liftLeft Z`, and $\Omega$ is `CrossEnsemble.operator`. The left side is a Lean `tsum`; the proof shows that the series converges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L1126-L1158

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
open ContinuousLinearMap
open scoped ENNReal
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem OAI.BeamLadder.output_weak (r : ℝ) (j : Fin n) (x : I → JointFock n) (z : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (he : CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)
        (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)=
      CrossEnsemble.operator (fun j => inverseWeight 3 (z j)) (fun j => inverseWeight 3 (z j)))
    (Z : Fock n →L[ℂ] Fock n) :
    (∑' i, weakL r j (x i) (x i) (liftLeft Z))=singleWeak r j z Z := by sorry
