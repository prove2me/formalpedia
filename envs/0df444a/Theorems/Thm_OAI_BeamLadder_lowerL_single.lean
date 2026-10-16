-- Prove2me | Theorems.Thm_OAI_BeamLadder_lowerL_single
-- name    : OAI.BeamLadder.lowerL_single
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:07:16.680876+00:00
-- url     : https://prove2.me/theorems/95b52a79-4204-4f5c-b4dd-70844e882f58
-- title:
--   Action of the weighted retained-port lowering operator on two-port number vectors
-- statement:
--   On the two-port space $\mathcal F_n^{(2)}=\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$, with number basis $|k,e\rangle$, put $W(k,e)=\nu(k)+\nu(e)-1=1+|k|+|e|$, where $\nu(k)=1+\sum_j k_j$ (so $W\ge 1$ is one plus the total photon number of both ports), and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$. The weighted lowering operator of mode $j$ on the first port is the bounded operator
--   $$
--   (L_jx)(k,e)=\frac{\sqrt{k_j+1}}{W(k,e)+1}\,x(k+e_j,e).
--   $$
--   For $a\in\mathbb{N}^n$ let $a^{\downarrow j}$ be $a$ with its $j$-th entry replaced by $\max(a_j-1,0)$.
--
--   **Theorem.** For every mode $j$ and all $a,b\in\mathbb{N}^n$,
--   $$
--   L_j\,|a,b\rangle=\frac{\sqrt{a_j}}{W(a,b)}\,\bigl|a^{\downarrow j},b\bigr\rangle .
--   $$
--   In particular $L_j|a,b\rangle=0$ when $a_j=0$.
--
--   Thus on number vectors $L_j$ acts as the annihilation operator $a_j\otimes1$ preceded by division by $W$, i.e. it is the bounded operator $(a_j\otimes 1)\,W^{-1}$. This basis formula is what reduces identities for $L_j$, such as its covariance under the beam splitter, to identities for matrix coefficients.
--
--   **Formalization Note** $|a,b\rangle$ is `lp.single 2 (a,b) 1`, $L_j$ is `BeamLadder.lowerL j`, and $a^{\downarrow j}$ is `Annihilation.down j a`, defined with truncated natural subtraction $a_j-1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L96-L115

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
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

theorem OAI.BeamLadder.lowerL_single (j : Fin n) (a b : NumberIndex n) :
    lowerL j (lp.single 2 (a,b) 1)=
      ((Real.sqrt (a j)/W (a,b):ℝ):ℂ) • lp.single 2 (down j a,b) 1 := by sorry
