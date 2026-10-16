-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_SpectralLogData_centeredEnergy_lowerEnergy
-- name    : OAI.EntropyPhotonNumber.SpectralLogData.centeredEnergy_lowerEnergy
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-16T02:53:37.252151+00:00
-- url     : https://prove2.me/theorems/62063188-723b-433f-8ade-1ea339ea5e79
-- title:
--   Centered annihilation energy equals mean mode occupation minus squared mean amplitude
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with annihilation operators $a_j$, number operators $\hat n_j=a_j^\dagger a_j$ and the weight $\hat N=1+\sum_j\hat n_j$ (diagonal, $\hat N|k\rangle=(1+|k|)|k\rangle$); states are positive operators on $F$ with number-basis diagonal summing to $1$. A *weighted column family* of a state $\mu$ is a family $(x_l)$ in $F$ with $\sum_l\|x_l\|^2<\infty$ such that $y_l=\hat N^{-3}x_l$ satisfy $\sum_l\|y_l\|^2=1$ and $\sum_l|y_l\rangle\langle y_l|=\mu$.
--
--   A *spectral logarithm datum* $G$ for a state $\rho$ consists (among other data) of an eigenbasis $(b_l)$ of $\rho$ with eigenvalues $p_l>0$, $\sum_lp_l=1$, and spectral columns $x_l$ with $\hat N^{-3}x_l=\sqrt{p_l}\,b_l$ (a weighted column family of $\rho$). For mode $j$ put $\mu_j=\sum_lp_l\langle b_l,a_jb_l\rangle$ (the mean of $a_j$) and $c_{lm}=\langle b_l,(a_j-\mu_j)b_m\rangle$.
--
--   For the spectral columns put $y_l=\hat N^{-3}x_l=\sqrt{p_l}\,b_l$ and define the *centered energy* and the *lower energy* of mode $j$ by
--   $$\mathcal E^{c}(G)=\sum_{j=1}^n\sum_l\bigl\|(a_j-\mu_j)\,y_l\bigr\|^2,\qquad \mathcal E_j=\sum_l\|a_j\,y_l\|^2 .$$
--
--   **Theorem.** For every $t>0$,
--   $$\mathcal E^{c}(G)=\sum_{j=1}^n\Bigl(\mathcal E_j-|\mu_j|^2\Bigr).$$
--
--   Formally $\mathcal E_j=\operatorname{Tr}\rho\,a_j^\dagger a_j$ and $\mu_j=\operatorname{Tr}\rho\,a_j$, so this is the variance identity $\operatorname{Tr}\rho(a_j-\mu_j)^\dagger(a_j-\mu_j)=\langle\hat n_j\rangle_\rho-|\langle a_j\rangle_\rho|^2$ summed over modes, proved in the regularized (weighted-column) setting where all vectors are honestly in $F$.
--
--   **Formalization Note** The vectors $(a_j-\mu)y_l$ and $a_jy_l$ are written as `centeredLadder j μ false (x l)` and `sandwich 0 3 j (x l)`; $\mathcal E_j$ is `G.weightedColumns.lowerEnergy j`. The parameter $t>0$ is used only through an auxiliary weak-mean identity and does not affect the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L470-L496

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.SpectralLogData
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
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem OAI.EntropyPhotonNumber.SpectralLogData.centeredEnergy_lowerEnergy (t : ℝ) (ht : 0<t) :
    G.centeredEnergy=∑ j, (G.weightedColumns.lowerEnergy j-‖G.annihilationMean j‖^2) := by sorry
