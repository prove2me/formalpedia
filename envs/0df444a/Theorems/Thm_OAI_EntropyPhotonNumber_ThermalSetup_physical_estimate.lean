-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_ThermalSetup_physical_estimate
-- name    : OAI.EntropyPhotonNumber.ThermalSetup.physical_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T03:00:46.539691+00:00
-- url     : https://prove2.me/theorems/0d36de8e-f0f9-46c9-9e6e-e4d545c5599d
-- title:
--   Defect estimate for the regularized output in terms of the input defects and means
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)$, $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, $\hat n_j=a_j^\dagger a_j$, and the diagonal weight $\hat N=1+\sum_j\hat n_j$ (so $\hat N|k\rangle=(1+|k|)|k\rangle$). States are positive operators on $F$ with number-basis diagonal summing to $1$; $E(\rho)=\sum_k|k|\rho_{kk}$, and $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$. For $r>0$, $\tau_r$ denotes the thermal state with mean photon number $r$ per mode, $\langle k|\tau_r|l\rangle=\delta_{kl}\prod_i\frac1{r+1}(\frac r{r+1})^{k_i}$, and $h(r)=\log(r+1)-\log r$.
--
--   *Thermal setup.* Fix $\eta,\theta,\kappa\in(0,1)$, $\varepsilon>0$, $d>0$, $r_1,r_2>0$, and put
--   $$r_0=\theta\bigl(\eta r_1+(1-\eta)r_2\bigr)+(1-\theta)d,\qquad w_1=(1-\kappa)\theta\eta,\qquad w_2=(1-\kappa)\theta(1-\eta).$$
--   Let $L$ be the logarithmic mean, $f(x)=x/\sinh x$, $w(r,\nu)=\frac{1}{h(r)}\frac{f(h(r)\nu/2)f(-h(r)/2)}{f(h(r)\nu/2-h(r)/2)}$ the thermal weight, $w_*(r)=\inf_\nu w(r,\nu)$ and $\chi(r)=(h(r)w_*(r))^{-1/2}$. The setup assumes the slack conditions
--   $$(1+\varepsilon)\bigl(\theta\eta r_1+\theta(1-\eta)r_2\bigr)\le r_0,\qquad(1+\varepsilon)\bigl(\theta\eta(r_1+1)+\theta(1-\eta)(r_2+1)\bigr)\le r_0+1,$$
--   and the smallness $\kappa\le\varepsilon^2/\bigl(4(\varepsilon+2)\chi(r_0)^2\bigr)$. For $\zeta>0$ the associated regularization uses transmissivities $\eta$ and $\theta$, environment $\tau_d$, replacement $\tau_{r_0}$ with weight $\kappa$, and constants $c=1/h(r_0)$, $a_i=(1+\varepsilon)w_i/h(r_i)$, $b_i=\varepsilon w_i$ and $\zeta$; its output is $\omega(\rho,\sigma)=(1-\kappa)\,\mathcal B_\theta(\mathcal B_\eta(\rho,\sigma),\tau_d)+\kappa\tau_{r_0}$ and its objective is $\Phi_\zeta(\rho,\sigma)=cS(\omega)-a_1S(\rho)-a_2S(\sigma)+b_1E(\rho)+\zeta M_4(\rho)+b_2E(\sigma)+\zeta M_4(\sigma)$.
--
--   For a spectral logarithm datum $G$ (eigenbasis $(b_l)$, eigenvalues $p_l$) of a state and a mode $j$, let $\mu_j=\sum_lp_l\langle b_l,a_jb_l\rangle$, $c_{lm}=\langle b_l,(a_j-\mu_j)b_m\rangle$, and for $t>0$ let $\Delta^{G,t}_j$ be the defect functional $x\mapsto\sum_{l,m}\frac{(t+1)p_m-tp_l}{\sqrt{m_{lm}}}\overline{c_{lm}}\,x_{lm}$, where $m_{lm}=h(t)L(p_l,p_m)w(t,\frac{\log p_l-\log p_m}{h(t)})$, restricted to the centered space (the orthogonal complement in $\ell^2$ of the vector with diagonal entries $\sqrt{p_l}$). Put
--   $$\mathsf D_t(G)=\sum_{j=1}^n\bigl\|\Delta^{G,t}_j\bigr\|^2,\qquad\mathsf M(G)=\sum_{j=1}^n|\mu_j|^2 .$$
--
--   For a basis $e$ and weights $v$ let $Q_{e,v}(T)=\sum_{i,l}L(v_i,v_l)|\langle e_i,Te_l\rangle|^2$ and $\mathrm c_{e,v}(T)=T-(\sum_iv_i\langle e_i,Te_i\rangle)\mathrm{Id}$, and let $\mathcal Z(e,v)$ be the span of $|e_i\rangle\langle e_l|-\delta_{il}v_i\mathrm{Id}$. Let $A_1(Z)$ be the partial expectation, over the second input in state $\sigma$, of the Heisenberg dual of the two-stage map (mix the inputs at $\eta$, then mix with $\tau_d$ at $\theta$, keep the retained port) applied to $Z$, and $A_2(Z)$ the partial expectation over the first input in state $\rho$.
--
--   **Theorem.** Let $\zeta>0$, let $\rho,\sigma$ be states with finite sixth moments, and let $G_1,G_2,G_0$ be spectral logarithm data of $\rho$, $\sigma$ and $\omega(\rho,\sigma)$ (bases $e^{(i)}$, probabilities $v^{(i)}$). Assume for all $Z\in\mathcal Z(e^{(0)},v^{(0)})$
--   $$(1-\kappa)^2Q_{e^{(1)},v^{(1)}}\bigl(\mathrm c_{e^{(1)},v^{(1)}}(A_1Z)\bigr)\le\frac{(1+\varepsilon)w_1/h(r_1)}{1/h(r_0)}\,Q_{e^{(0)},v^{(0)}}(Z),\qquad(1-\kappa)^2Q_{e^{(2)},v^{(2)}}\bigl(\mathrm c_{e^{(2)},v^{(2)}}(A_2Z)\bigr)\le\frac{(1+\varepsilon)w_2/h(r_2)}{1/h(r_0)}\,Q_{e^{(0)},v^{(0)}}(Z).$$
--   Then
--   $$\mathsf D_{r_0}(G_0)\le w_1\mathsf D_{r_1}(G_1)+w_2\mathsf D_{r_2}(G_2)+\frac\varepsilon2\Bigl(w_1\mathsf D_{r_1}(G_1)+w_2\mathsf D_{r_2}(G_2)+w_1\mathsf M(G_1)+w_2\mathsf M(G_2)\Bigr).$$
--
--   So the total thermal-balance defect of the output is controlled by the weighted input defects, with an $\varepsilon/2$ relative loss that also involves the input means; this is one half of the cancellation argument for the minimizers.
--
--   **Formalization Note** The data are the structure `ThermalSetup` and its regularization `P.reg n ζ hζ`; $\mathsf D_t$ and $\mathsf M$ are `defectSquared` and `meanSquared`; $A_1,A_2$ are `rawFirstSlice P.η P.θ … σ (thermalState n P.d P.hd)` and `rawSecondSlice … ρ …`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L1312-L1371

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.ThermalSetup
open scoped BigOperators ComplexConjugate
open QuantumTrace ThermalMetric Annihilation
variable {n : ℕ} (P : ThermalSetup)

theorem OAI.EntropyPhotonNumber.ThermalSetup.physical_estimate (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n)
    (G1 : SpectralLogData n ρ) (G2 : SpectralLogData n σ)
    (G0 : SpectralLogData n ((P.reg n ζ hζ).output ρ σ))
    (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ)
    (hh1 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic G1.basis G1.probability
        (BKM.center G1.basis G1.probability (rawFirstSlice P.η P.θ P.η_mem P.θ_mem σ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w1/h P.r1)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z)
    (hh2 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic G2.basis G2.probability
        (BKM.center G2.basis G2.probability (rawSecondSlice P.η P.θ P.η_mem P.θ_mem ρ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w2/h P.r2)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z) :
    G0.defectSquared P.r0 P.r0_pos≤
      P.w1*G1.defectSquared P.r1 P.hr1+P.w2*G2.defectSquared P.r2 P.hr2+
      P.ε/2*(P.w1*G1.defectSquared P.r1 P.hr1+P.w2*G2.defectSquared P.r2 P.hr2+
        (P.w1*G1.meanSquared+P.w2*G2.meanSquared)) := by sorry
