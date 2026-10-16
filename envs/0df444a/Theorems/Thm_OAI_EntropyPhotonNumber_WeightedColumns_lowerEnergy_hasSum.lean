-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_lowerEnergy_hasSum
-- name    : OAI.EntropyPhotonNumber.WeightedColumns.lowerEnergy_hasSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:55:07.991283+00:00
-- url     : https://prove2.me/theorems/1cd24f5d-79bd-48d3-a54e-48a6ba7c2022
-- title:
--   Lower ladder energy of weighted columns equals the mean occupation of the mode
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with annihilation operators $a_j$, number operators $\hat n_j=a_j^\dagger a_j$ and the weight $\hat N=1+\sum_j\hat n_j$ (diagonal, $\hat N|k\rangle=(1+|k|)|k\rangle$); states are positive operators on $F$ with number-basis diagonal summing to $1$. A *weighted column family* of a state $\mu$ is a family $(x_l)$ in $F$ with $\sum_l\|x_l\|^2<\infty$ such that $y_l=\hat N^{-3}x_l$ satisfy $\sum_l\|y_l\|^2=1$ and $\sum_l|y_l\rangle\langle y_l|=\mu$.
--
--   For a weighted column family $x$ of a state $\rho$ and a mode $j$ define the *lower energy*
--   $$\mathcal E_j(x)=\sum_l\bigl\|a_j\,\hat N^{-3}x_l\bigr\|^2=\sum_l\|a_jy_l\|^2 .$$
--
--   **Theorem.** For every state $\rho$, every weighted column family $x$ of $\rho$ and every mode $j$, the series $\sum_{k\in\mathbb{N}^n}k_j\,\langle k|\rho|k\rangle$ converges and
--   $$\sum_{k\in\mathbb{N}^n}k_j\,\langle k|\rho|k\rangle=\mathcal E_j(x).$$
--
--   So the lower energy does not depend on the chosen column family: it is the mean photon number $\operatorname{Tr}\rho\,\hat n_j$ of mode $j$, which in particular is finite whenever $\rho$ admits weighted columns.
--
--   **Formalization Note** The conclusion is a `HasSum` statement for the real parts of the diagonal entries `entry ρ.op k k`; $\mathcal E_j(x)$ is `X.lowerEnergy j`, a `tsum` of `‖sandwich 0 3 j (X.vector l)‖^2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L520-L542

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
variable {n : ℕ} {ρ : State n}

theorem OAI.EntropyPhotonNumber.WeightedColumns.lowerEnergy_hasSum (X : WeightedColumns ρ) (j : Fin n) :
    HasSum (fun k => (k j:ℝ)*(entry ρ.op k k).re) (X.lowerEnergy j) := by sorry
