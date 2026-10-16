-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_negativeLog_le_thermal
-- name    : OAI.EntropyPhotonNumber.negativeLog_le_thermal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:47:16.859088+00:00
-- url     : https://prove2.me/theorems/63a397b9-638d-4e03-90ae-498678258359
-- title:
--   Thermal domination bounds the $-\log\rho$ form by norm and photon number
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ with number basis $|k\rangle$ and $|k|=k_1+\dots+k_n$. For $r>0$ let $\tau_r$ be the thermal state, diagonal with entries $w_r(k)=\prod_{j=1}^n\frac1{r+1}\big(\frac r{r+1}\big)^{k_j}$. Let $\rho$ be a state with $\kappa\,\tau_r\le\rho$ (operator order) for some $0<\kappa\le1$, and let $(b_j)_{j\in J}$ be a Hilbert eigenbasis of $\rho$, $\rho b_j=p_jb_j$, with $p_j>0$ and $\sum_jp_j=1$. Let $x\in\mathcal F_n$ have finite energy, i.e. $\mathcal E(x)=\sum_k|k|\,|\langle k|x\rangle|^2<\infty$. Then the series $\sum_j(-\log p_j)|\langle b_j,x\rangle|^2$ converges and
--
--   $$
--   \sum_{j\in J}(-\log p_j)\,|\langle b_j,x\rangle|^2\le\big(-\log\kappa+n\log(r+1)\big)\|x\|^2+\log\frac{r+1}{r}\;\mathcal E(x).
--   $$
--
--   In operator language, $-\log\rho\le\big(-\log\kappa+n\log(r+1)\big)1+\log\frac{r+1}r\,\hat N$ on finite-energy vectors, where $\hat N$ is the total number operator: thermal domination controls the logarithm of the state by the photon number. This is the basic estimate behind bounded representations of $-\log\rho$ after energy regularization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean#L694-L713

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

theorem OAI.EntropyPhotonNumber.negativeLog_le_thermal {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (x : Fock n) (hx : FiniteVectorEnergy x) :
    Summable (fun j => -Real.log (p j)*‖inner ℂ (b j) x‖^2) ∧
      (∑' j, -Real.log (p j)*‖inner ℂ (b j) x‖^2) ≤
        (-Real.log κ+n*Real.log (r+1))*‖x‖^2+Real.log ((r+1)/r)*vectorEnergy x := by sorry
