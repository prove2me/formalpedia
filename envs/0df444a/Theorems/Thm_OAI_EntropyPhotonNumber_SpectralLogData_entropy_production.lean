-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_SpectralLogData_entropy_production
-- name    : OAI.EntropyPhotonNumber.SpectralLogData.entropy_production
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:45:04.894985+00:00
-- url     : https://prove2.me/theorems/407e2bda-5dea-4f7c-bf32-91e487a02275
-- title:
--   Entropy-production identity for the thermal generator in the eigenbasis of a state
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode Fock space with number basis $|k\rangle$, $|k|=k_1+\dots+k_n$, let $\mathcal N$ be multiplication by $1+|k|$, $a_j$ the annihilation operator of mode $j$, and $\rho$ a state (positive, unit number-basis trace) with finite sixth moment $\sum_k(1+|k|)^6\langle k|\rho|k\rangle<\infty$. Put $x_k=\mathcal N^3\rho^{1/2}|k\rangle$ ($k\in\mathbb N^n$); this family is square-summable and $\rho=\sum_k|\mathcal N^{-3}x_k\rangle\langle\mathcal N^{-3}x_k|$.
--
--   *Generator pairing.* For $t\in\mathbb R$, a square-summable family $x=(x_i)$ and a bounded $Z$, let $G_j^-=\mathcal N^2a_j\mathcal N^{-3}$, $G_j^+=\mathcal N^2a_j^\dagger\mathcal N^{-3}$ (bounded), let $M_j^-$, $M_j^+$ be multiplication by $k_j/(1+|k|)$ and $(k_j+1)/(1+|k|)$, and put $\mathcal D_j^\pm(x;Z)=\sum_i\big(\langle G_j^\pm x_i,ZG_j^\pm x_i\rangle-\tfrac12\langle\mathcal N^{-1}x_i,ZM_j^\pm x_i\rangle-\tfrac12\langle M_j^\pm x_i,Z\mathcal N^{-1}x_i\rangle\big)$ and $P_t(x;Z)=\sum_{j=1}^n\big((t+1)\mathcal D_j^-(x;Z)+t\,\mathcal D_j^+(x;Z)\big)$.
--
--   *Spectral data.* Let $\mathcal G$ consist of an orthonormal eigenbasis $(b_l)_{l\in J}$ of $\rho$ with eigenvalues $p_l>0$, $\sum_lp_l=1$; square-summable vectors $(y_l)$ with $\mathcal N^{-3}y_l=\sqrt{p_l}\,b_l$; and a bounded symmetric operator $L$ with $\operatorname{Re}\langle y,Ly\rangle=\sum_l(-\log p_l)|\langle b_l,\mathcal N^{-2}y\rangle|^2$ for all $y$ and $L(\mathcal N^{-1}y_l)=(-\log p_l)\mathcal N^{-5}y_l$. Set $A_j(l,r)=p_r^{-1/2}\langle b_l,a_j\mathcal N^{-3}y_r\rangle$, $\mu_j=\sum_rp_rA_j(r,r)$, $C_j(l,r)=A_j(l,r)-\delta_{lr}\mu_j$, and the centered energy $K=\sum_j\sum_r\|(a_j-\mu_j)\mathcal N^{-3}y_r\|^2$.
--
--   *Thermal metric.* For $t>0$ let $h(t)=\log(t+1)-\log t$, $c_t(p,q)=(t+1)q-tp$, and let $m_t(p,q)>0$ be the thermal metric coefficient. On $\ell^2(J\times J)$ let $\mathcal C_t$ be the orthogonal complement of the vector $u(l,r)=\delta_{lr}\sqrt{m_t(p_l,p_l)}$, and let $D_{t,j}$ be the functional $v\mapsto\langle d_{t,j},v\rangle$ restricted to $\mathcal C_t$, where $d_{t,j}(l,r)=c_t(p_l,p_r)\,m_t(p_l,p_r)^{-1/2}\,C_j(l,r)$.
--
--   Then for every $t>0$,
--
--   $$
--   \frac{\operatorname{Re}P_t(x;L)}{h(t)}=\sum_{j=1}^n\|D_{t,j}\|^2-\big(K-n\,t\big).
--   $$
--
--   Formally $P_t(x;Z)$ is $\operatorname{Tr}\big[(\mathcal N^2Z\mathcal N^2)\,\mathcal L_t(\rho)\big]$ for the thermal Lindblad generator $\mathcal L_t=\sum_j\big((t+1)\mathcal D[a_j]+t\,\mathcal D[a_j^\dagger]\big)$, and $L$ is a bounded version of $\mathcal N^{-2}(-\log\rho)\mathcal N^{-2}$, so the left side is a regularized entropy-production rate of $\rho$ under the thermal semigroup. The identity splits it into a nonnegative defect term and the centered energy minus $nt$.
--
--   **Formalization Note** $\mathcal G$ is the structure `SpectralLogData n ρ`; $x$ is `weightedRoot 3 ρ hm`, $P_t$ is `WeightedGenerator.pairing`, $\|D_{t,j}\|$ is the operator norm of `G.defect t ht j` on the closed subspace `centeredSpace`, and $K$ is `G.centeredEnergy`. The coefficient $m_t$ is `ThermalMetric.metricCoefficient`, a positive product of $h(t)$, the logarithmic mean of $p,q$ and a positive weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean#L309-L326

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.SpectralLogData
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
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem OAI.EntropyPhotonNumber.SpectralLogData.entropy_production (hm : FiniteMoment 6 ρ) (t : ℝ) (ht : 0<t) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re/h t =
      (∑ j, ‖G.defect t ht j‖^2)-(G.centeredEnergy-(n:ℝ)*t) := by sorry
