-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_regularizedOutput_energy_bound
-- name    : OAI.EntropyPhotonNumber.regularizedOutput_energy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:53:50.12089+00:00
-- url     : https://prove2.me/theorems/9159c427-ab17-4f90-8fb4-221b62b3e21d
-- title:
--   Energy bound for the regularized beam-splitter output
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode Fock space with number basis $|k\rangle$, $k\in\mathbb N^n$, and $|k|=k_1+\dots+k_n$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ whose number-basis diagonal sums to $1$; its energy is $E(\rho)=\sum_k|k|\,\langle k|\rho|k\rangle$, and $\rho$ has finite energy if this series converges. For $\eta\in[0,1]$ and states $\rho,\sigma$, let $\mathrm{BS}_\eta(\rho,\sigma)$ be the reduced state on the first output port of $U_\eta(\rho\otimes\sigma)U_\eta^*$, where $U_\eta$ is the passive beam-splitter unitary of transmissivity $\eta$ acting identically on every pair of modes. For $\eta,\delta,\kappa\in[0,1]$ and states $\tau_D,\tau_0$ the regularized output is
--
--   $$
--   \Gamma(\rho,\sigma)=(1-\kappa)\,\mathrm{BS}_{1-\delta}\big(\mathrm{BS}_\eta(\rho,\sigma),\tau_D\big)+\kappa\,\tau_0 .
--   $$
--
--   If $\tau_D,\tau_0,\rho,\sigma$ all have finite energy, then
--
--   $$
--   E\big(\Gamma(\rho,\sigma)\big)\le E(\rho)+E(\sigma)+E(\tau_D)+E(\tau_0).
--   $$
--
--   The regularized output perturbs the physical beam-splitter output by a second, weak beam splitter with a reference state $\tau_D$ and a small admixture of $\tau_0$; the bound shows that this regularization keeps energies under control, which is needed for continuity of the output entropy on energy-bounded sets.
--
--   **Formalization Note** $\Gamma$ is `regularizedOutput η δ κ ... τD τ0 ρ σ`, built from `beamOutput` (a partial trace of the mixed product state) and `mixture`. The energy is a `tsum`, which is why finiteness is assumed for all four states.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1236-L1252

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
open QuantumTrace Filter Topology

theorem OAI.EntropyPhotonNumber.regularizedOutput_energy_bound {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) {τD τ0 ρ σ : State n}
    (hD : FiniteEnergy τD) (h0 : FiniteEnergy τ0) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ σ) ≤
      energy ρ+energy σ+energy τD+energy τ0 := by sorry
