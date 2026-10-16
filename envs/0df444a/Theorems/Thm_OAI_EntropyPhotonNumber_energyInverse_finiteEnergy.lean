-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_energyInverse_finiteEnergy
-- name    : OAI.EntropyPhotonNumber.energyInverse_finiteEnergy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:59:48.956948+00:00
-- url     : https://prove2.me/theorems/7179a81e-1870-48fc-a1d8-bd9ffd30f358
-- title:
--   The operator $(1+\hat N)^{-1/2}$ maps every Fock vector to a finite-energy vector
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ with number basis $|k\rangle$ and $|k|=k_1+\dots+k_n$, and let $\mathcal N^{-1/2}$ be the bounded multiplication operator $(\mathcal N^{-1/2}x)(k)=(1+|k|)^{-1/2}x(k)$. For every $x\in\mathcal F_n$ the vector $\mathcal N^{-1/2}x$ has finite energy, i.e. the series
--
--   $$
--   \mathcal E\big(\mathcal N^{-1/2}x\big)=\sum_{k\in\mathbb N^n}|k|\,\big|\langle k|\mathcal N^{-1/2}x\rangle\big|^2
--   $$
--
--   converges.
--
--   In operator language, $\hat N^{1/2}(1+\hat N)^{-1/2}$ is bounded, where $\hat N$ is the total photon-number operator. This allows energy-weighted forms such as $\mathcal E$ or the thermal bound for $-\log\rho$ to be evaluated on $\mathcal N^{-1/2}x$ for arbitrary $x$, which is the regularization used to represent such forms by bounded operators.
--
--   **Formalization Note** $\mathcal N^{-1/2}$ is `energyInverse n`, and finite energy of a vector is `FiniteVectorEnergy`, summability of $|k|\,|\langle k|y\rangle|^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1753-L1764

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
open QuantumTrace TensorLp

theorem OAI.EntropyPhotonNumber.energyInverse_finiteEnergy {n : ℕ} (x : Fock n) : FiniteVectorEnergy (energyInverse n x) := by sorry
