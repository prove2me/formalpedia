-- Prove2me | Theorems.Thm_OAI_BeamLadder_discarded_covariance
-- name    : OAI.BeamLadder.discarded_covariance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:10:54.936615+00:00
-- url     : https://prove2.me/theorems/94c0e622-e5ea-4ec9-a443-d139f6ee06f7
-- title:
--   Beam-splitter covariance of the weighted discarded-port lowering operator
-- statement:
--   On the two-port space $\mathcal F_n^{(2)}=\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$, with number basis $|k,e\rangle$, put $W(k,e)=\nu(k)+\nu(e)-1=1+|k|+|e|$, where $\nu(k)=1+\sum_j k_j$ (so $W\ge 1$ is one plus the total photon number of both ports), and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$.
--
--   The weighted lowering operators $L_j$ (first, retained port) and $R_j$ (second, discarded port) of mode $j$ are the bounded operators
--   $$
--   (L_jx)(k,e)=\frac{\sqrt{k_j+1}}{W(k,e)+1}\,x(k+e_j,e),\qquad (R_jx)(k,e)=\frac{\sqrt{e_j+1}}{W(k,e)+1}\,x(k,e+e_j).
--   $$
--
--   For a real parameter $\eta$ and $k,e,a,b\in\mathbb{N}$ the one-mode beam-splitter coefficient is $\beta_\eta(k,e;a,b)=0$ unless $k+e=a+b$, in which case
--   $$
--   \beta_\eta(k,e;a,b)=\sqrt{\frac{k!\,e!}{a!\,b!}}\sum_{\substack{0\le p\le a,\ 0\le q\le b\\ p+q=k}}\binom{a}{p}\binom{b}{q}\sqrt{\eta}^{\,p}\bigl(-\sqrt{1-\eta}\bigr)^{a-p}\sqrt{1-\eta}^{\,q}\sqrt{\eta}^{\,b-q},
--   $$
--   and for multi-indices $k,e,a,b\in\mathbb{N}^n$ one sets $\beta_\eta(k,e;a,b)=\prod_{j}\beta_\eta(k_j,e_j;a_j,b_j)$.
--
--   For $\eta\in[0,1]$, $U_\eta$ denotes the passive beam-splitter unitary (a linear isometric equivalence) of $\mathcal F_n^{(2)}$ constructed blockwise on total-number sectors; its number-basis matrix entries are $\langle k,e|U_\eta|a,b\rangle=\beta_\eta(k,e;a,b)$.
--
--   **Theorem.** For every $\eta\in[0,1]$ and every mode $j$, as bounded operators on $\mathcal F_n^{(2)}$,
--   $$
--   R_j\,U_\eta=U_\eta\bigl(-\sqrt{1-\eta}\,L_j+\sqrt{\eta}\,R_j\bigr).
--   $$
--
--   Heuristically $L_j=(a_j\otimes1)W^{-1}$ and $R_j=(1\otimes a_j)W^{-1}$ with $W$ commuting with $U_\eta$, so the identity is a bounded, number-weighted form of the mode transformation $U_\eta^{\dagger}(1\otimes a_j)U_\eta=-\sqrt{1-\eta}\,a_j\otimes1+\sqrt{\eta}\,1\otimes a_j$ for the discarded output port, the second row of the rotation $\begin{pmatrix}\sqrt\eta&\sqrt{1-\eta}\\-\sqrt{1-\eta}&\sqrt\eta\end{pmatrix}$.
--
--   **Formalization Note** $L_j$, $R_j$ are `BeamLadder.lowerL j`, `BeamLadder.lowerR j`, and $U_\eta$ is `EntropyPhotonNumber.beamUnitary η hη` viewed as a continuous linear map; both sides are compositions of continuous linear maps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L214-L237

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

theorem OAI.BeamLadder.discarded_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    lowerR j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • lowerL j+(Real.sqrt η:ℂ) • lowerR j) := by sorry
