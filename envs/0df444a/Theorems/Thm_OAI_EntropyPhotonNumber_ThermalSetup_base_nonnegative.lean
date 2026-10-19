-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_ThermalSetup_base_nonnegative
-- name    : OAI.EntropyPhotonNumber.ThermalSetup.base_nonnegative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T03:03:37.996372+00:00
-- url     : https://prove2.me/theorems/4222186d-c8f2-4a1c-a417-cdadc2985ffe
-- title:
--   Penalized tangent form of the entropy photon-number inequality for fixed thermal references
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space; a state is a positive operator on $F$ whose number-basis diagonal sums to $1$. Write $S(\rho)=-\operatorname{Tr}\rho\log\rho$ for the von Neumann entropy, $E(\rho)=\sum_k|k|\,\rho_{kk}$ for the mean total photon number, $g(t)=(t+1)\log(t+1)-t\log t$, $h(r)=\log(r+1)-\log r$, $\tau_r$ for the thermal state with mean photon number $r$ in each mode, and $\mathcal B_\theta(\rho,\sigma)$ for the beam-splitter output at transmissivity $\theta$ (the same passive rotation in every mode, retained port).
--
--   *Thermal setup.* Fix $\eta,\theta,\kappa\in(0,1)$, $\varepsilon>0$, $d>0$, $r_1,r_2>0$, and put
--   $$r_0=\theta\bigl(\eta r_1+(1-\eta)r_2\bigr)+(1-\theta)d,\qquad w_1=(1-\kappa)\theta\eta,\qquad w_2=(1-\kappa)\theta(1-\eta).$$
--   With $L$ the logarithmic mean, $f(x)=x/\sinh x$, $w(r,\nu)=\frac1{h(r)}\frac{f(h(r)\nu/2)f(-h(r)/2)}{f(h(r)\nu/2-h(r)/2)}$, $w_*(r)=\inf_\nu w(r,\nu)$ and $\chi(r)=(h(r)w_*(r))^{-1/2}$, assume
--   $$(1+\varepsilon)\bigl(\theta\eta r_1+\theta(1-\eta)r_2\bigr)\le r_0,\quad(1+\varepsilon)\bigl(\theta\eta(r_1+1)+\theta(1-\eta)(r_2+1)\bigr)\le r_0+1,\quad\kappa\le\frac{\varepsilon^2}{4(\varepsilon+2)\chi(r_0)^2}.$$
--   For states $\rho,\sigma$ let $\omega(\rho,\sigma)=(1-\kappa)\,\mathcal B_\theta\bigl(\mathcal B_\eta(\rho,\sigma),\tau_d\bigr)+\kappa\,\tau_{r_0}$ and define
--   $$\mathcal P(\rho,\sigma)=\frac{S(\omega)-n\,g(r_0)}{h(r_0)}-w_1\frac{S(\rho)-n\,g(r_1)}{h(r_1)}-w_2\frac{S(\sigma)-n\,g(r_2)}{h(r_2)},$$
--   $$\Pi(\rho,\sigma)=\varepsilon\Bigl(\frac{w_1}{h(r_1)}T_{r_1}(\rho)+\frac{w_2}{h(r_2)}T_{r_2}(\sigma)\Bigr),\qquad T_r(\rho)=n\log(r+1)+h(r)E(\rho)-S(\rho).$$
--
--   **Theorem.** For all states $\rho,\sigma$ with finite fourth moments, $\sum_k(1+|k|)^4\rho_{kk}<\infty$ and likewise for $\sigma$,
--   $$0\le\mathcal P(\rho,\sigma)+\Pi(\rho,\sigma).$$
--
--   Here $n\log(r+1)+h(r)E(\rho)$ is the cross-entropy $-\operatorname{Tr}\rho\log\tau_r$, so $T_r(\rho)$ is the relative entropy of $\rho$ with respect to $\tau_r$, and $\mathcal P$ compares the entropies with the tangent lines of $g$ at the reference parameters, since $g'=h$. The statement is the penalized, regularized tangent inequality from which the entropy photon-number inequality is obtained by letting $\kappa,\varepsilon\to0$ and $\theta\to1$.
--
--   **Formalization Note** The setup is the structure `ThermalSetup`; $\mathcal P$, $\Pi$, $T_r$ are `P.entropyPart`, `P.penalty`, `thermalRelative`; $\omega$ is `P.out`, the output of the regularization `P.reg n 1 _` (the output does not depend on the regularization parameter $\zeta$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalLimit.lean#L678-L722

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalLimit

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.ThermalSetup
open scoped BigOperators ComplexConjugate Topology
open QuantumTrace ThermalMetric Filter
variable {n : ℕ} (P : ThermalSetup)

theorem OAI.EntropyPhotonNumber.ThermalSetup.base_nonnegative {ρw σw : State n} (hw1 : FiniteMoment 4 ρw) (hw2 : FiniteMoment 4 σw) :
    0≤P.entropyPart ρw σw+P.penalty ρw σw := by sorry
