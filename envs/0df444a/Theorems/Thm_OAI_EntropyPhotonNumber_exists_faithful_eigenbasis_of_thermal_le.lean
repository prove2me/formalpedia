-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_exists_faithful_eigenbasis_of_thermal_le
-- name    : OAI.EntropyPhotonNumber.exists_faithful_eigenbasis_of_thermal_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:46:48.294254+00:00
-- url     : https://prove2.me/theorems/4ce1f5a5-f19f-4a23-beed-a0f10071ed62
-- title:
--   A state dominating a multiple of a thermal state has a faithful eigenbasis
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ with number basis $|k\rangle$. For $r>0$ let $\tau_r$ be the thermal state with parameter $r$, the diagonal operator with entries
--   $w_r(k)=\prod_{j=1}^n\frac1{r+1}\big(\frac r{r+1}\big)^{k_j}$. Let $\rho$ be a state on $\mathcal F_n$ (a positive bounded operator whose number-basis diagonal sums to $1$) and let $\kappa>0$ with
--
--   $$
--   \kappa\,\tau_r\le\rho
--   $$
--
--   in the operator order. Then there exist an index type $J$, a Hilbert (orthonormal) basis $(b_j)_{j\in J}$ of $\mathcal F_n$ and numbers $p_j$ such that $p_j>0$ for every $j$, $\sum_jp_j=1$ (as a convergent series), and $\rho\,b_j=p_j\,b_j$ for all $j$.
--
--   So a state that dominates a positive multiple of a thermal state is diagonalizable with strictly positive eigenvalues (it is faithful), which is what makes $-\log\rho$ meaningful on its eigenbasis.
--
--   **Formalization Note** The order is the Loewner order on continuous linear maps, $\kappa\tau_r\le\rho$ meaning that $\rho-\kappa\tau_r$ is positive. No upper bound on $\kappa$ is required.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean#L650-L671

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

open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open QuantumTrace

theorem OAI.EntropyPhotonNumber.exists_faithful_eigenbasis_of_thermal_le {n : ℕ} (ρ : State n)
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op) :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ ∀ j, ρ.op (b j) = (p j : ℂ) • b j := by sorry
