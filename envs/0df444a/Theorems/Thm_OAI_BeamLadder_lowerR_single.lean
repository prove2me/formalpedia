-- Prove2me | Theorems.Thm_OAI_BeamLadder_lowerR_single
-- name    : OAI.BeamLadder.lowerR_single
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:08:31.16873+00:00
-- url     : https://prove2.me/theorems/e03a9aae-c7b6-40ef-bddf-1111d57338fe
-- title:
--   Action of the weighted discarded-port lowering operator on two-port number vectors
-- statement:
--   On the two-port space $\mathcal F_n^{(2)}=\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$, with number basis $|k,e\rangle$, put $W(k,e)=\nu(k)+\nu(e)-1=1+|k|+|e|$, where $\nu(k)=1+\sum_j k_j$ (so $W\ge 1$ is one plus the total photon number of both ports), and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$. The weighted lowering operator of mode $j$ on the second port is the bounded operator
--   $$
--   (R_jx)(k,e)=\frac{\sqrt{e_j+1}}{W(k,e)+1}\,x(k,e+e_j).
--   $$
--   For $b\in\mathbb{N}^n$ let $b^{\downarrow j}$ be $b$ with its $j$-th entry replaced by $\max(b_j-1,0)$.
--
--   **Theorem.** For every mode $j$ and all $a,b\in\mathbb{N}^n$,
--   $$
--   R_j\,|a,b\rangle=\frac{\sqrt{b_j}}{W(a,b)}\,\bigl|a,b^{\downarrow j}\bigr\rangle .
--   $$
--   In particular $R_j|a,b\rangle=0$ when $b_j=0$.
--
--   Thus on number vectors $R_j$ acts as $(1\otimes a_j)\,W^{-1}$, the annihilation operator on the second port preceded by division by $W$. This basis formula is the input for the beam-splitter covariance identities of the lowering operators.
--
--   **Formalization Note** $|a,b\rangle$ is `lp.single 2 (a,b) 1`, $R_j$ is `BeamLadder.lowerR j`, and $b^{\downarrow j}$ is `Annihilation.down j b`, defined with truncated natural subtraction $b_j-1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L117-L136

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

theorem OAI.BeamLadder.lowerR_single (j : Fin n) (a b : NumberIndex n) :
    lowerR j (lp.single 2 (a,b) 1)=
      ((Real.sqrt (b j)/W (a,b):ℝ):ℂ) • lp.single 2 (a,down j b) 1 := by sorry
