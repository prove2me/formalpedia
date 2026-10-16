-- Prove2me | Theorems.Thm_OAI_BeamLadder_radial_covariance
-- name    : OAI.BeamLadder.radial_covariance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:11:24.478826+00:00
-- url     : https://prove2.me/theorems/4064ef2d-6285-42e1-ae3c-4e13bc1b3fbf
-- title:
--   Bounded functions of the total photon number commute with the beam-splitter unitary
-- statement:
--   On the two-port space $\mathcal F_n^{(2)}=\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$, with number basis $|k,e\rangle$, put $W(k,e)=\nu(k)+\nu(e)-1=1+|k|+|e|$, where $\nu(k)=1+\sum_j k_j$ (so $W\ge 1$ is one plus the total photon number of both ports), and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$.
--
--   For a real parameter $\eta$ and $k,e,a,b\in\mathbb{N}$ the one-mode beam-splitter coefficient is $\beta_\eta(k,e;a,b)=0$ unless $k+e=a+b$, in which case
--   $$
--   \beta_\eta(k,e;a,b)=\sqrt{\frac{k!\,e!}{a!\,b!}}\sum_{\substack{0\le p\le a,\ 0\le q\le b\\ p+q=k}}\binom{a}{p}\binom{b}{q}\sqrt{\eta}^{\,p}\bigl(-\sqrt{1-\eta}\bigr)^{a-p}\sqrt{1-\eta}^{\,q}\sqrt{\eta}^{\,b-q},
--   $$
--   and for multi-indices $k,e,a,b\in\mathbb{N}^n$ one sets $\beta_\eta(k,e;a,b)=\prod_{j}\beta_\eta(k_j,e_j;a_j,b_j)$.
--
--   For $\eta\in[0,1]$, $U_\eta$ denotes the passive beam-splitter unitary (a linear isometric equivalence) of $\mathcal F_n^{(2)}$ constructed blockwise on total-number sectors; its number-basis matrix entries are $\langle k,e|U_\eta|a,b\rangle=\beta_\eta(k,e;a,b)$.
--
--   Let $f:\mathbb{R}\to\mathbb{R}$ and $C\ge0$ with $|f(W(k,e))|\le C$ for all $(k,e)\in\mathbb{N}^n\times\mathbb{N}^n$, and let $f(W)$ be the bounded diagonal operator $(f(W)x)(k,e)=f(W(k,e))\,x(k,e)$.
--
--   **Theorem.** For every $\eta\in[0,1]$,
--   $$
--   f(W)\,U_\eta=U_\eta\,f(W).
--   $$
--
--   Because the beam splitter is passive, it preserves total photon number, and so it commutes with every bounded function of $W$. This is used to move weights such as $W^{-1}$ or $W/(W-1)$ through the beam splitter when computing reduced output states.
--
--   **Formalization Note** $f(W)$ is `BeamLadder.radial f C hC hf`; the bound $C$ and its hypotheses only serve to make the diagonal operator bounded. $U_\eta$ is `beamUnitary η hη` as a continuous linear map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean#L266-L284

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
open scoped ComplexConjugate
variable {n : ℕ}

theorem OAI.BeamLadder.radial_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C) :
    radial f C hC hf ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L radial f C hC hf := by sorry
