-- Prove2me | Theorems.Thm_OAI_BeamLadder_coefficient_W
-- name    : OAI.BeamLadder.coefficient_W
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:09:01.605989+00:00
-- url     : https://prove2.me/theorems/1d942e36-0f72-4c16-b5b5-b98511e06d6e
-- title:
--   Nonzero beam-splitter coefficients conserve total photon number
-- statement:
--   For a real parameter $\eta$ and $k,e,a,b\in\mathbb{N}$ the one-mode beam-splitter coefficient is $\beta_\eta(k,e;a,b)=0$ unless $k+e=a+b$, in which case
--   $$
--   \beta_\eta(k,e;a,b)=\sqrt{\frac{k!\,e!}{a!\,b!}}\sum_{\substack{0\le p\le a,\ 0\le q\le b\\ p+q=k}}\binom{a}{p}\binom{b}{q}\sqrt{\eta}^{\,p}\bigl(-\sqrt{1-\eta}\bigr)^{a-p}\sqrt{1-\eta}^{\,q}\sqrt{\eta}^{\,b-q},
--   $$
--   and for multi-indices $k,e,a,b\in\mathbb{N}^n$ one sets $\beta_\eta(k,e;a,b)=\prod_{j}\beta_\eta(k_j,e_j;a_j,b_j)$.
--
--   For $k,e\in\mathbb{N}^n$ put $W(k,e)=\nu(k)+\nu(e)-1=1+\sum_j k_j+\sum_j e_j$, where $\nu(k)=1+\sum_j k_j$.
--
--   **Theorem.** Let $\eta\in\mathbb{R}$ and $k,e,a,b\in\mathbb{N}^n$. If $\beta_\eta(k,e;a,b)\neq0$, then
--   $$
--   W(k,e)=W(a,b).
--   $$
--
--   Since $\beta_\eta(k,e;a,b)$ are the number-basis matrix entries of the passive beam-splitter unitary, this says that the beam splitter never connects number vectors with different total photon number. It is the selection rule behind the commutation of the beam splitter with functions of $W$ and behind the beam-splitter covariance of the weighted ladder operators.
--
--   **Formalization Note** $\beta_\eta$ on multi-indices is `EntropyPhotonNumber.beamCoefficient`, built from `oneModeBeamCoefficient`; $W$ is `BeamLadder.W`. No restriction on $\eta$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L138-L151

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

theorem OAI.BeamLadder.coefficient_W (η : ℝ) (k e a b : NumberIndex n) (hc : beamCoefficient η k e a b ≠ 0) :
    W (k,e)=W (a,b) := by sorry
