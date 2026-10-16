-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_exists_minimum
-- name    : OAI.EntropyPhotonNumber.Regularization.exists_minimum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:56:10.175857+00:00
-- url     : https://prove2.me/theorems/926259f0-517f-4de2-8a85-bce0bfd4bd22
-- title:
--   Existence of a minimizer for the regularized entropy photon-number objective
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode Fock space with number basis $|k\rangle$, $k\in\mathbb N^n$, and $|k|=k_1+\dots+k_n$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ whose number-basis diagonal sums to $1$; its energy is $E(\rho)=\sum_k|k|\,\langle k|\rho|k\rangle$, and $\rho$ has finite energy if this series converges. The von Neumann entropy is $S(\rho)=\sum_k\langle k|{-\rho\log\rho}|k\rangle$ (with $0\log0=0$) and the fourth number moment is $M_4(\rho)=\sum_k(1+|k|)^4\langle k|\rho|k\rangle$.
--
--   A *regularization* $\mathcal R$ consists of parameters $\eta,\delta,\kappa\in[0,1]$, finite-energy states $\tau_D,\tau_0$, and positive constants $c,a_1,a_2,b_1,b_2,\zeta>0$. Its output map is $\Gamma(\rho,\sigma)=(1-\kappa)\mathrm{BS}_{1-\delta}(\mathrm{BS}_\eta(\rho,\sigma),\tau_D)+\kappa\tau_0$, where $\mathrm{BS}_\eta(\rho,\sigma)$ is the first-port reduced state of the beam-splitter mixing $U_\eta(\rho\otimes\sigma)U_\eta^*$. The objective and the entropy constant are
--   $$\mathcal J(\rho,\sigma)=c\,S(\Gamma(\rho,\sigma))-a_1S(\rho)-a_2S(\sigma)+b_1E(\rho)+\zeta M_4(\rho)+b_2E(\sigma)+\zeta M_4(\sigma),$$
--   $$K_{\mathcal R}=a_1n\log\Big(\frac{2a_1}{b_1}+1\Big)+a_2n\log\Big(\frac{2a_2}{b_2}+1\Big).$$
--
--   Let $\rho_w,\sigma_w$ be states with finite fourth moment, $M_4(\rho_w)<\infty$ and $M_4(\sigma_w)<\infty$. Then there exist states $\rho,\sigma$ with finite fourth moment such that $\mathcal J(\rho,\sigma)\le\mathcal J(\rho_w,\sigma_w)$ and
--
--   $$
--   \mathcal J(\rho,\sigma)\le\mathcal J(\rho',\sigma')\qquad\text{for all states }\rho',\sigma'\text{ with finite fourth moment.}
--   $$
--
--   So the regularized objective attains its infimum over pairs of states with finite fourth moment; the given pair $(\rho_w,\sigma_w)$ only serves as a witness that the relevant sublevel set is nonempty. Optimizers of such regularized problems are the objects on which first-order (variational) conditions can be derived in the proof of the entropy photon-number inequality.
--
--   **Formalization Note** "Finite fourth moment" is `FiniteMoment 4`, i.e. summability of $(1+|k|)^4\langle k|\rho|k\rangle$; it implies finite energy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1504-L1521

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

theorem OAI.EntropyPhotonNumber.Regularization.exists_minimum (ρw σw : State n) (hw1 : FiniteMoment 4 ρw) (hw2 : FiniteMoment 4 σw) :
    ∃ ρ σ : State n, FiniteMoment 4 ρ ∧ FiniteMoment 4 σ ∧
      R.objective ρ σ ≤ R.objective ρw σw ∧
      ∀ ρ' σ' : State n, FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
        R.objective ρ σ ≤ R.objective ρ' σ' := by sorry
