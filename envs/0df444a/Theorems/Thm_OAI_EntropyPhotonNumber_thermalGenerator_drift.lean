-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_thermalGenerator_drift
-- name    : OAI.EntropyPhotonNumber.thermalGenerator_drift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:49:18.329194+00:00
-- url     : https://prove2.me/theorems/30f282c9-f45b-48c1-9168-dc2346259768
-- title:
--   On diagonal observables the thermal generator acts through the birth-death drift
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ with number basis $|k\rangle$, $|k|=k_1+\dots+k_n$, let $\mathcal N$ be multiplication by $1+|k|$ and $a_j$ the annihilation operator of mode $j$; write $\mathbf 1_j$ for the $j$-th unit index. For $r\in\mathbb R$ and $f:\mathbb N^n\to\mathbb R$ define the drift
--   $$(\mathcal A_rf)(k)=\sum_{j=1}^n\Big((r+1)\,k_j\big(f(k-\mathbf 1_j)-f(k)\big)+r\,(k_j+1)\big(f(k+\mathbf 1_j)-f(k)\big)\Big).$$
--   For a square-summable family $x=(x_i)$ and bounded $Z$ define the generator pairing $P_r(x;Z)=\sum_j\big((r+1)\mathcal D_j^-(x;Z)+r\,\mathcal D_j^+(x;Z)\big)$, where $\mathcal D_j^\pm(x;Z)=\sum_i\big(\langle G_j^\pm x_i,ZG_j^\pm x_i\rangle-\frac12\langle\mathcal N^{-1}x_i,ZM_j^\pm x_i\rangle-\frac12\langle M_j^\pm x_i,Z\mathcal N^{-1}x_i\rangle\big)$ with $G_j^-=\mathcal N^2a_j\mathcal N^{-3}$, $G_j^+=\mathcal N^2a_j^\dagger\mathcal N^{-3}$ and $M_j^\pm$ multiplication by $(k_j+\tfrac12\pm\tfrac12)/(1+|k|)$.
--
--   Let $\rho$ be a state with $\sum_k(1+|k|)^6\langle k|\rho|k\rangle<\infty$, let $x_k=\mathcal N^3\rho^{1/2}|k\rangle$, and let $f$, $C\ge0$ and $D$ satisfy $|f(k)/(1+|k|)^4|\le C$ and $|(\mathcal A_rf)(k)/(1+|k|)^6|\le D$ for all $k$. Let $D_f$ be multiplication by $f(k)/(1+|k|)^4$. Then the series below converges and
--
--   $$
--   \sum_{k\in\mathbb N^n}(\mathcal A_rf)(k)\,\langle k|\rho|k\rangle=\operatorname{Re}P_r\big(x;D_f\big).
--   $$
--
--   Formally, $P_r(x;Z)$ is $\operatorname{Tr}[(\mathcal N^2Z\mathcal N^2)\mathcal L_r(\rho)]$ for the thermal generator $\mathcal L_r=\sum_j((r+1)\mathcal D[a_j]+r\mathcal D[a_j^\dagger])$, so with $\mathcal N^2D_f\mathcal N^2=f(\hat N)$ the identity says that $\operatorname{Tr}[f\,\mathcal L_r(\rho)]=\sum_k(\mathcal A_rf)(k)\rho_{kk}$: on diagonal observables the quantum generator acts as the classical birth-death generator $\mathcal A_r$ on the photon-number distribution.
--
--   **Formalization Note** At $k_j=0$ the index $k-\mathbf 1_j$ is read with truncated subtraction, which is harmless since it is multiplied by $k_j=0$. The family $x$ is `weightedRoot 3 ρ hm`, $P_r$ is `WeightedGenerator.pairing`, and $\mathcal A_r$ is `WeightedGenerator.drift`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L240-L271

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
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

theorem OAI.EntropyPhotonNumber.thermalGenerator_drift (r : ℝ) (ρ : State n) (hm : FiniteMoment 6 ρ)
    (f : NumberIndex n → ℝ) (C D : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C)
    (hd : ∀ k, |WeightedGenerator.drift r f k/numberWeight k^6| ≤ D) :
    HasSum (fun k => WeightedGenerator.drift r f k*(entry ρ.op k k).re)
      (WeightedGenerator.pairing r (weightedRoot 3 ρ hm)
        (diagonal (fun k => f k/numberWeight k^4) C hC hf)).re := by sorry
