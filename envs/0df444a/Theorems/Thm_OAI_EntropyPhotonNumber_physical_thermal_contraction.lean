-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_physical_thermal_contraction
-- name    : OAI.EntropyPhotonNumber.physical_thermal_contraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:28:23.54145+00:00
-- url     : https://prove2.me/theorems/3e4f4077-ac87-4af2-b45b-db5d1591c812
-- title:
--   Thermal-weight contraction for the conditional slices of a two-stage beam splitter
-- statement:
--   **Setting.** Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space; a state is a positive operator on $F$ whose number-basis diagonal sums to $1$. For $\eta\in[0,1]$ and states $\rho,\sigma$ let $\mathcal B_\eta(\rho,\sigma)$ be the beam-splitter output: the reduced state of the retained port after the passive rotation with transmissivity $\eta$ is applied in every mode to $\rho\otimes\sigma$. For $\theta\in[0,1]$ and a state $\tau$ let $\Phi$ be the two-stage map that sends a two-port input $\omega_{12}$ (an operator on $\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$) to the retained port of the $\eta$-beam splitter, mixes this with $\tau$ in a $\theta$-beam splitter and keeps the retained port; thus $\Phi(\rho\otimes\sigma)=\mathcal B_\theta(\mathcal B_\eta(\rho,\sigma),\tau)$. Let $\Phi^*$ be its Heisenberg-picture dual. For a bounded $Z$ on $F$ define the conditional slices
--   $$\langle x,A_1(Z)x'\rangle=\sum_{k}\bigl\langle x\otimes\sqrt\sigma|k\rangle,\ \Phi^*(Z)\,(x'\otimes\sqrt\sigma|k\rangle)\bigr\rangle,\qquad \langle y,A_2(Z)y'\rangle=\sum_{k}\bigl\langle \sqrt\rho|k\rangle\otimes y,\ \Phi^*(Z)\,(\sqrt\rho|k\rangle\otimes y')\bigr\rangle ,$$
--   the partial expectations of $\Phi^*(Z)$ over the second input in state $\sigma$, respectively over the first input in state $\rho$.
--
--   **Spectral data.** A thermal spectral datum $\mathcal S=(e,p,r)$ is a Hilbert basis $(e_k)$ of $F$, weights $p_k>0$ with $\sum_kp_k=1$, and $r>0$. Put $h(r)=\log(r+1)-\log r$, $\nu_{kl}=(\log p_k-\log p_l)/h(r)$, let $L$ be the logarithmic mean and $f(x)=x/\sinh x$, $f(0)=1$. Define
--   $$Q_{\mathcal S}(T)=\sum_{k,l}L(p_k,p_l)\,|\langle e_k,Te_l\rangle|^2,\qquad \mathrm{c}_{\mathcal S}(T)=T-\Bigl(\sum_kp_k\langle e_k,Te_k\rangle\Bigr)\mathrm{Id},$$
--   the thermal weight $w(r,\nu)=\frac{1}{h(r)}\,\frac{f(h(r)\nu/2)\,f(-h(r)/2)}{f(h(r)\nu/2-h(r)/2)}$, and
--   $$Q^{\mathcal S}_{w}(T)=\sum_{k,l}w(r,\nu_{kl})\,h(r)\,L(p_k,p_l)\,|\langle e_k,Te_l\rangle|^2 .$$
--   Let $\mathcal Z(\mathcal S)$ be the complex span of the operators $|e_k\rangle\langle e_l|-\delta_{kl}p_k\mathrm{Id}$.
--
--   **Theorem.** Let $\eta,\theta,\kappa\in[0,1]$ with $\kappa<1$, let $\varepsilon\in\mathbb{R}$, let $\rho,\sigma,\tau,\omega$ be states, let $\mathcal S_0,\mathcal S_1,\mathcal S_2$ be thermal spectral data (weights $p^{(i)}$, parameters $r_i$) and $\lambda_1,\lambda_2>0$. Assume
--
--   1. $\rho\,e^{(1)}_k=p^{(1)}_k e^{(1)}_k$ and $\sigma\,e^{(2)}_k=p^{(2)}_k e^{(2)}_k$ for all $k$;
--   2. $\sum_kp^{(0)}_k|e^{(0)}_k\rangle\langle e^{(0)}_k|=(1-\kappa)\,\mathcal B_\theta\bigl(\mathcal B_\eta(\rho,\sigma),\tau\bigr)+\kappa\,\omega$;
--   3. for $i=1,2$ and all $Z\in\mathcal Z(\mathcal S_0)$: $\ (1-\kappa)^2\,Q_{\mathcal S_i}\bigl(\mathrm c_{\mathcal S_i}(A_iZ)\bigr)\le(1+\varepsilon)(1-\kappa)\,\lambda_i\,\dfrac{h(r_0)}{h(r_i)}\,Q_{\mathcal S_0}(Z)$;
--   4. $(1+\varepsilon)(\lambda_1r_1+\lambda_2r_2)\le r_0$ and $(1+\varepsilon)\bigl(\lambda_1(r_1+1)+\lambda_2(r_2+1)\bigr)\le r_0+1$.
--
--   Then for every $Z\in\mathcal Z(\mathcal S_0)$, with the normalized slices $N_i(Z)=\lambda_i^{-1/2}\,\mathrm c_{\mathcal S_i}(A_iZ)$,
--   $$\sum_{i=1}^{2}(1-\kappa)\,\lambda_i\;Q^{\mathcal S_i}_{w}\bigl(N_iZ\bigr)\;\le\;Q^{\mathcal S_0}_{w}(Z).$$
--
--   This is the contraction of the thermal metric under the two conditional slices of the beam-splitter dual: plain Hessian bounds (hypothesis 3) together with the slack conditions on the reference parameters (hypothesis 4) are upgraded to the same inequality for the non-constant thermal weight $w$.
--
--   **Formalization Note** The data $\mathcal S_i$ are `ThermalSpectral.Space (Fock n)`; $A_1,A_2$ are `rawFirstSlice`, `rawSecondSlice`; $N_i$ is `normalizedSlices`; $Q_{\mathcal S}$ is `BKM.quadratic`, $\mathrm c_{\mathcal S}$ is `BKM.center`, $Q^{\mathcal S}_w$ is `Space.pquad thermalWeight`, and the weight $w$ is `ThermalMetric.weight` $=$ `fourWeightTarget (1/h r) (h r ν/2) (-h r/2)`. Hypothesis 2 is stated through the ensemble $(\sqrt{p_k}\,e_k)$ of $\mathcal S_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Contraction.lean#L851-L886

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
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

theorem OAI.EntropyPhotonNumber.physical_thermal_contraction (η θ κ ε : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ < 1)
    (ρ σ τ ω : State n) (S₀ : Space (Fock n)) (S : Fin 2 → Space (Fock n))
    (lam : Fin 2 → ℝ) (hlam : ∀ i, 0 < lam i)
    (he₁ : ∀ j, ρ.op ((S 0).basis j)=((S 0).p j:ℂ) • (S 0).basis j)
    (he₂ : ∀ j, σ.op ((S 1).basis j)=((S 1).p j:ℂ) • (S 1).basis j)
    (he₀ : TraceEnsemble.operator S₀.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)^2*BKM.quadratic (S 0).basis (S 0).p
        (BKM.center (S 0).basis (S 0).p (rawFirstSlice η θ hη hθ σ τ Z)) ≤
      (1+ε)*(1-κ)*lam 0*(h S₀.r/h (S 0).r)*BKM.quadratic S₀.basis S₀.p Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)^2*BKM.quadratic (S 1).basis (S 1).p
        (BKM.center (S 1).basis (S 1).p (rawSecondSlice η θ hη hθ ρ τ Z)) ≤
      (1+ε)*(1-κ)*lam 1*(h S₀.r/h (S 1).r)*BKM.quadratic S₀.basis S₀.p Z)
    (hr : (1+ε)*(∑ i, lam i*(S i).r) ≤ S₀.r)
    (hs : (1+ε)*(∑ i, lam i*((S i).r+1)) ≤ S₀.r+1)
    (Z : Fock n →L[ℂ] Fock n) (hZ : Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p) :
    ∑ i, ((1-κ)*lam i)*(S i).pquad thermalWeight
      (normalizedSlices η θ hη hθ ρ σ τ S lam i Z) ≤ S₀.pquad thermalWeight Z := by sorry
