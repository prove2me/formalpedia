-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_beamOutput_powerMoment_le
-- name    : OAI.EntropyPhotonNumber.beamOutput_powerMoment_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:13:23.90107+00:00
-- url     : https://prove2.me/theorems/071aee44-b352-4b0e-9f24-c3f22eb12b10
-- title:
--   Polynomial photon-number moments are submultiplicative under the beam splitter
-- statement:
--   Throughout, $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ is the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, and $|k|=k_1+\dots+k_n$ is the total photon number of $k$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ with $\sum_k\langle k|\rho|k\rangle=1$.
--
--   For $m\in\mathbb{N}$ and a state $\rho$, the $m$-th number moment is
--   $$
--   P_m(\rho)=\sum_{k\in\mathbb{N}^n}(1+|k|)^m\,\langle k|\rho|k\rangle\in[0,\infty].
--   $$
--   For $\eta\in[0,1]$, let $U_\eta$ be the beam-splitter unitary of transmissivity $\eta$ on the two-port space $\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$. In each mode it mixes the two ports with the rotation $\begin{pmatrix}\sqrt\eta&-\sqrt{1-\eta}\\\sqrt{1-\eta}&\sqrt\eta\end{pmatrix}$, acting blockwise on the sectors of fixed per-mode total photon number $k_j+l_j$. The beam-splitter output of two states $\rho_A,\rho_B$ is the state
--   $$
--   \rho_C=\operatorname{Tr}_2\bigl[U_\eta(\rho_A\otimes\rho_B)U_\eta^{*}\bigr],
--   $$
--   the partial trace over the second output port.
--
--   **Theorem.** For all $n$, $\eta\in[0,1]$, $m\in\mathbb{N}$ and all states $\rho_A,\rho_B$ on $\mathcal F_n$,
--   $$
--   P_m(\rho_C)\le P_m(\rho_A)\,P_m(\rho_B)\qquad\text{in }[0,\infty].
--   $$
--
--   No finiteness assumption is needed. In particular, if both inputs have finite $m$-th moment, so does the output. This propagation of moment bounds through the beam splitter is used to keep the output state in the regularity class needed for the entropy estimates.
--
--   **Formalization Note** The output state is built from vectors: $\rho_C$ is the partial trace of the ensemble $U_\eta\bigl(\sqrt{\rho_A}|a\rangle\otimes\sqrt{\rho_B}|b\rangle\bigr)$, $(a,b)\in\mathbb{N}^n\times\mathbb{N}^n$, which represents $U_\eta(\rho_A\otimes\rho_B)U_\eta^*$. $P_m$ is `powerMoment m`, valued in `ℝ≥0∞`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L917-L962

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational

open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open TensorLp

theorem OAI.EntropyPhotonNumber.beamOutput_powerMoment_le {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (m : ℕ) (ρA ρB : State n) :
    powerMoment m (beamOutput η hη ρA ρB) ≤ powerMoment m ρA*powerMoment m ρB := by sorry
