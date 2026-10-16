-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_thermal_lowerEnergy
-- name    : OAI.EntropyPhotonNumber.WeightedColumns.thermal_lowerEnergy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:57:09.155987+00:00
-- url     : https://prove2.me/theorems/9b2f4820-487a-4ea3-b8bc-207bcfde8c3d
-- title:
--   The thermal state has lower energy $r$ in every mode
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with annihilation operators $a_j$, number operators $\hat n_j=a_j^\dagger a_j$ and the weight $\hat N=1+\sum_j\hat n_j$ (diagonal, $\hat N|k\rangle=(1+|k|)|k\rangle$); states are positive operators on $F$ with number-basis diagonal summing to $1$. A *weighted column family* of a state $\mu$ is a family $(x_l)$ in $F$ with $\sum_l\|x_l\|^2<\infty$ such that $y_l=\hat N^{-3}x_l$ satisfy $\sum_l\|y_l\|^2=1$ and $\sum_l|y_l\rangle\langle y_l|=\mu$.
--
--   For a weighted column family $x$ of a state $\rho$ and a mode $j$ let $\mathcal E_j(x)=\sum_l\|a_j\hat N^{-3}x_l\|^2$ be its lower energy.
--
--   **Theorem.** Let $r>0$ and let $\rho$ be the $n$-mode thermal state with mean photon number $r$ per mode, i.e.
--   $$\langle k|\rho|l\rangle=\delta_{kl}\prod_{i=1}^n\frac1{r+1}\Bigl(\frac r{r+1}\Bigr)^{k_i}\qquad(k,l\in\mathbb{N}^n).$$
--   Then for every weighted column family $x$ of $\rho$ and every mode $j$,
--   $$\mathcal E_j(x)=r .$$
--
--   This confirms that the regularized ladder energy reproduces the familiar mean occupation $\operatorname{Tr}\rho\,\hat n_j=r$ of a thermal state; it is used when thermal reference states enter the energy bookkeeping.
--
--   **Formalization Note** The thermal hypothesis is stated entrywise in the number basis via `QuantumTrace.thermalWeight n r k` $=\prod_i(r+1)^{-1}(r/(r+1))^{k_i}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L559-L578

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
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.WeightedColumns
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Metric
open MeasureTheory Set Filter Topology Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology MeasureTheory
open QuantumTrace Annihilation
variable {n : ℕ}

theorem OAI.EntropyPhotonNumber.WeightedColumns.thermal_lowerEnergy {ρ : State n} (X : WeightedColumns ρ) (r : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0) (j : Fin n) :
    X.lowerEnergy j=r := by sorry
