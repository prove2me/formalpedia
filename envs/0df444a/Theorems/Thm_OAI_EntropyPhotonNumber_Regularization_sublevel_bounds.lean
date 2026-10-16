-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_sublevel_bounds
-- name    : OAI.EntropyPhotonNumber.Regularization.sublevel_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:54:52.140307+00:00
-- url     : https://prove2.me/theorems/3d8da116-012f-418f-ae66-4d23c2b5ebd7
-- title:
--   Sublevel sets of the regularized entropy objective have bounded energy and fourth moment
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode Fock space with number basis $|k\rangle$, $k\in\mathbb N^n$, and $|k|=k_1+\dots+k_n$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ whose number-basis diagonal sums to $1$; its energy is $E(\rho)=\sum_k|k|\,\langle k|\rho|k\rangle$, and $\rho$ has finite energy if this series converges. The von Neumann entropy is $S(\rho)=\sum_k\langle k|{-\rho\log\rho}|k\rangle$ (with $0\log0=0$) and the fourth number moment is $M_4(\rho)=\sum_k(1+|k|)^4\langle k|\rho|k\rangle$.
--
--   A *regularization* $\mathcal R$ consists of parameters $\eta,\delta,\kappa\in[0,1]$, finite-energy states $\tau_D,\tau_0$, and positive constants $c,a_1,a_2,b_1,b_2,\zeta>0$. Its output map is $\Gamma(\rho,\sigma)=(1-\kappa)\mathrm{BS}_{1-\delta}(\mathrm{BS}_\eta(\rho,\sigma),\tau_D)+\kappa\tau_0$, where $\mathrm{BS}_\eta(\rho,\sigma)$ is the first-port reduced state of the beam-splitter mixing $U_\eta(\rho\otimes\sigma)U_\eta^*$. The objective and the entropy constant are
--   $$\mathcal J(\rho,\sigma)=c\,S(\Gamma(\rho,\sigma))-a_1S(\rho)-a_2S(\sigma)+b_1E(\rho)+\zeta M_4(\rho)+b_2E(\sigma)+\zeta M_4(\sigma),$$
--   $$K_{\mathcal R}=a_1n\log\Big(\frac{2a_1}{b_1}+1\Big)+a_2n\log\Big(\frac{2a_2}{b_2}+1\Big).$$
--
--   Let $C\in\mathbb R$ and let $\rho,\sigma$ be finite-energy states with $\mathcal J(\rho,\sigma)\le C$. Then
--
--   1. $0\le C+K_{\mathcal R}$;
--   2. $E(\rho)\le2(C+K_{\mathcal R})/b_1$ and $E(\sigma)\le2(C+K_{\mathcal R})/b_2$;
--   3. $M_4(\rho)\le(C+K_{\mathcal R})/\zeta$ and $M_4(\sigma)\le(C+K_{\mathcal R})/\zeta$.
--
--   This is the coercivity of the regularized objective: on a sublevel set the energies and fourth moments of both inputs are uniformly bounded. It confines the minimization to a compact set of states, which is the first step of the direct method used to produce optimizers for the entropy photon-number problem.
--
--   **Formalization Note** $\mathcal R$ is the structure `Regularization n`, $\mathcal J$ is `R.objective`, $K_{\mathcal R}$ is `R.entropyConstant`, $E$ is `energy` and $M_4$ is `numberMoment 4`; entropy, energy and moments are `tsum`s.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1460-L1477

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Regularization
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
variable {n : ℕ} (R : Regularization n)

theorem OAI.EntropyPhotonNumber.Regularization.sublevel_bounds (C : ℝ) (ρ σ : State n) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ)
    (h : R.objective ρ σ ≤ C) :
    0 ≤ C+R.entropyConstant ∧
    energy ρ ≤ 2*(C+R.entropyConstant)/R.b1 ∧
    energy σ ≤ 2*(C+R.entropyConstant)/R.b2 ∧
    numberMoment 4 ρ ≤ (C+R.entropyConstant)/R.ζ ∧
    numberMoment 4 σ ≤ (C+R.entropyConstant)/R.ζ := by sorry
