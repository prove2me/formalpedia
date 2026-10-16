-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_negativeLog_extended_le_thermal
-- name    : OAI.EntropyPhotonNumber.negativeLog_extended_le_thermal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:58:51.151433+00:00
-- url     : https://prove2.me/theorems/d069e795-0fc6-48d5-9ba0-f9fe2458cc52
-- title:
--   Extended-valued bound of the $-\log\rho$ form by norm and photon number
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode Fock space with number basis $|k\rangle$, $k\in\mathbb N^n$, and $|k|=k_1+\dots+k_n$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ whose number-basis diagonal sums to $1$; its energy is $E(\rho)=\sum_k|k|\,\langle k|\rho|k\rangle$, and $\rho$ has finite energy if this series converges. For $r>0$ let $\tau_r$ be the thermal state, the diagonal operator with entries $w_r(k)=\prod_{j=1}^n\frac1{r+1}\big(\frac r{r+1}\big)^{k_j}$. Let $\rho$ be a state with $\kappa\,\tau_r\le\rho$ (operator order) for some $r>0$ and $0<\kappa\le1$, and let $(b_j)_{j\in J}$ be a Hilbert (orthonormal) eigenbasis of $\rho$, $\rho\,b_j=p_jb_j$, with $p_j>0$ and $\sum_jp_j=1$. For $x\in\mathcal F_n$ define the extended-valued quantities (in $[0,\infty]$)
--   $$\Lambda_\rho(x)=\sum_{j\in J}(-\log p_j)\,|\langle b_j,x\rangle|^2,\qquad\mathcal E(x)=\sum_{k}|k|\,|\langle k|x\rangle|^2 .$$
--   Then for every $x\in\mathcal F_n$, without any finiteness assumption,
--
--   $$
--   \Lambda_\rho(x)\le\big(-\log\kappa+n\log(r+1)\big)\,\|x\|^2+\log\frac{r+1}{r}\;\mathcal E(x)\quad\text{in }[0,\infty].
--   $$
--
--   This is the version of the thermal-domination bound for $-\log\rho$ that holds for all vectors: when $x$ has infinite energy the right-hand side is $+\infty$. Working in $[0,\infty]$ allows the bound to be summed over families of vectors (for instance over the outputs of a Kraus family) without tracking summability.
--
--   **Formalization Note** The sums are `ENNReal` series: $\Lambda_\rho(x)$ is `basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) x` and $\mathcal E(x)$ is `numberVectorMoment x`; the constants are embedded with `ENNReal.ofReal`. Both constants are nonnegative under the hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1619-L1637

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
open QuantumTrace

theorem OAI.EntropyPhotonNumber.negativeLog_extended_le_thermal {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (x : Fock n) :
    basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) x ≤
      ENNReal.ofReal (-Real.log κ+n*Real.log (r+1))*ENNReal.ofReal (‖x‖^2)+
      ENNReal.ofReal (Real.log ((r+1)/r))*numberVectorMoment x := by sorry
