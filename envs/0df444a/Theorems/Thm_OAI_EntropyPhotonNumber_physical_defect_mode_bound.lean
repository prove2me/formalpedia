-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_physical_defect_mode_bound
-- name    : OAI.EntropyPhotonNumber.physical_defect_mode_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:52:14.400897+00:00
-- url     : https://prove2.me/theorems/24337390-9c9e-48a8-9393-4d7be542b4c2
-- title:
--   Per-mode bound for the output thermal-balance defect by the input defects
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with annihilation operators $a_j$, number operators $\hat n_j=a_j^\dagger a_j$ and the weight $\hat N=1+\sum_j\hat n_j$ (diagonal, $\hat N|k\rangle=(1+|k|)|k\rangle$); states are positive operators on $F$ with number-basis diagonal summing to $1$. A *weighted column family* of a state $\mu$ is a family $(x_l)$ in $F$ with $\sum_l\|x_l\|^2<\infty$ such that $y_l=\hat N^{-3}x_l$ satisfy $\sum_l\|y_l\|^2=1$ and $\sum_l|y_l\rangle\langle y_l|=\mu$.
--
--   Put $h(r)=\log(r+1)-\log r$ for $r>0$, let $L$ be the logarithmic mean ($L(x,y)=\frac{y-x}{\log y-\log x}$, $L(x,x)=x$), $f(x)=x/\sinh x$ ($f(0)=1$), and let
--   $$w(r,\nu)=\frac1{h(r)}\,\frac{f(h(r)\nu/2)\,f(-h(r)/2)}{f(h(r)\nu/2-h(r)/2)}$$
--   be the thermal weight. A *thermal spectral datum* $\mathcal S=(e,p,r)$ on $F$ is a Hilbert basis $(e_k)_{k\in I}$, weights $p_k>0$ with $\sum_kp_k=1$, and $r>0$; put $\nu_{kl}=(\log p_k-\log p_l)/h(r)$ and $m_{kl}=h(r)\,L(p_k,p_l)\,w(r,\nu_{kl})>0$. Its *observable map* sends a bounded operator $Z$ to
--   $$\mathrm{obs}_{\mathcal S}(Z)=\Bigl(\sqrt{m_{kl}}\,\langle e_k,Ze_l\rangle\Bigr)_{k,l}\in\ell^2(I\times I),$$
--   so that $\|\mathrm{obs}_{\mathcal S}(Z)\|^2=Q^{\mathcal S}_w(Z):=\sum_{k,l}m_{kl}|\langle e_k,Ze_l\rangle|^2$. The *centered space* $\mathcal C(\mathcal S)\subseteq\ell^2(I\times I)$ is the orthogonal complement of $\mathrm{obs}_{\mathcal S}(\mathrm{Id})$ (the vector with diagonal entries $\sqrt{p_k}$ and zero off-diagonal entries), and $\mathcal Z(\mathcal S)$ is the span of the operators $|e_k\rangle\langle e_l|-\delta_{kl}p_k\mathrm{Id}$. Finally let $w_*(r)=\inf_{\nu\in\mathbb{R}}w(r,\nu)$ (which is $\ge r>0$) and $\chi(r)=\bigl(h(r)\,w_*(r)\bigr)^{-1/2}$.
--
--   A *spectral logarithm datum* $G$ for a state $\rho$ consists (among other data) of an eigenbasis $(b_l)$ of $\rho$ with eigenvalues $p_l>0$, $\sum_lp_l=1$, and spectral columns $x_l$ with $\hat N^{-3}x_l=\sqrt{p_l}\,b_l$ (a weighted column family of $\rho$). For mode $j$ put $\mu_j=\sum_lp_l\langle b_l,a_jb_l\rangle$ (the mean of $a_j$) and $c_{lm}=\langle b_l,(a_j-\mu_j)b_m\rangle$.
--
--   For $t>0$ let $\mathcal S_G(t)$ be the thermal spectral datum $(b,p,t)$ and $d_{lm}=(t+1)p_m-tp_l$. The *defect functional* of $G$ at $t$ in mode $j$ is the bounded functional on $\ell^2$
--   $$\Delta^{G,t}_j(x)=\sum_{l,m}\frac{d_{lm}}{\sqrt{m_{lm}}}\,\overline{c_{lm}}\,x_{lm},$$
--   so that $\Delta^{G,t}_j(\mathrm{obs}(Z))=\sum_{l,m}d_{lm}\overline{c_{lm}}\langle b_l,Zb_m\rangle$ is a weak form of the thermal balance $(t+1)a_j$ versus $t\,a_j^\dagger$. Write $\|\Delta^{G,t}_j\|$ for the norm of $\Delta^{G,t}_j$ restricted to the centered space $\mathcal C(\mathcal S_G(t))$.
--
--   **Setting.** Let $\eta,\theta\in(0,1)$, $\kappa\in[0,1)$, $\varepsilon\in\mathbb{R}$, $d>0$, $a_0,a_1>0$. Let $\rho_0,\rho_1,\tau_D,m,\gamma,\omega,\rho^\circ$ be states with $m=\mathcal B_\eta(\rho_0,\rho_1)$ and $\gamma=\mathcal B_\theta(m,\tau_D)$ (beam-splitter output relations). For $\eta\in[0,1]$ and states $\rho_0,\rho_1$, write $\mathcal B_\eta(\rho_0,\rho_1)$ for the beam-splitter output (the reduced state of the retained port after the passive rotation of transmissivity $\eta$ in every mode applied to $\rho_0\otimes\rho_1$). Put $\lambda_0=\theta\eta$, $\lambda_1=\theta(1-\eta)$ and $r_0=\theta(\eta a_0+(1-\eta)a_1)+(1-\theta)d$. For a bounded $Z$ let $A_0(Z)$ be the partial expectation, over the second input in state $\rho_1$, of the Heisenberg dual of the two-stage map (mix the two inputs at $\eta$, then mix the result with $\tau_D$ at $\theta$, keep the retained port) applied to $Z$, and $A_1(Z)$ the analogous partial expectation over the first input in state $\rho_0$. With $\mathrm c_i(T)=T-(\sum_lp^{(i)}_l\langle b^{(i)}_l,Tb^{(i)}_l\rangle)\mathrm{Id}$ the centering in the eigenbasis of $\rho_i$, the normalized slices are $N_i(Z)=\lambda_i^{-1/2}\,\mathrm c_i(A_iZ)$. Assume $r_0>0$, that $\tau_D$ and $\omega$ are number-diagonal thermal states with means $d$ and $r_0$ per mode, and $\rho^\circ=(1-\kappa)\gamma+\kappa\omega$. Let $G_0,G_1,G^\circ$ be spectral logarithm data for $\rho_0,\rho_1,\rho^\circ$ (with eigenbases $b^{(i)},b^\circ$ and eigenvalues $p^{(i)},p^\circ$), and let $y^V=(\hat N^{-3}v_l)$ come from a weighted column family $v$ of $\gamma$ (weighted column families of $\tau_D$, $m$ and $\omega$ are also given). For a basis $b$ and weights $p$ let $Q_{b,p}(T)=\sum_{k,l}L(p_k,p_l)|\langle b_k,Tb_l\rangle|^2$. Assume the Hessian bounds: for $i=0,1$ and all $Z\in\mathcal Z(b^\circ,p^\circ)$,
--   $$(1-\kappa)^2\,Q_{b^{(i)},p^{(i)}}\bigl(\mathrm c_i(A_iZ)\bigr)\le(1+\varepsilon)(1-\kappa)\,\lambda_i\,\frac{h(r_0)}{h(a_i)}\,Q_{b^\circ,p^\circ}(Z),$$
--   and the slack conditions $(1+\varepsilon)(\lambda_0a_0+\lambda_1a_1)\le r_0$ and $(1+\varepsilon)(\lambda_0(a_0+1)+\lambda_1(a_1+1))\le r_0+1$.
--
--   **Theorem.** For every mode $j$,
--   $$\bigl\|\Delta^{G^\circ,r_0}_j\bigr\|\le\sqrt{\sum_{i=0}^1(1-\kappa)\lambda_i\,\bigl\|\Delta^{G_i,a_i}_j\bigr\|^2}+\sqrt{(1-\kappa)\kappa}\;\bigl|\overline W\bigr|\;\chi(r_0),$$
--   where $\overline W=(r_0+1)\sum_l\langle a_jy^V_l,y^V_l\rangle-r_0\sum_l\langle y^V_l,a_j^\dagger y^V_l\rangle$ is the weak mean of $\gamma$ in mode $j$.
--
--   This controls the thermal-balance defect of the regularized output by those of the inputs, up to the error caused by the thermal replacement; it is the per-mode estimate that is later aggregated over modes.
--
--   **Formalization Note** $\|\Delta^{G,t}_j\|$ is the norm of `G.defect t ht j`; $Q_{b,p}$ is `BKM.quadratic`, $\mathrm c_i$ is `BKM.center`, $A_0,A_1$ are `rawFirstSlice`, `rawSecondSlice`, $\lambda$ is `twoPortLambda η θ`, $r_0$ is `outputReference η θ a d`, $\chi$ is `mixtureConstant`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L109-L180

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

open OAI OAI.EntropyPhotonNumber
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
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem OAI.EntropyPhotonNumber.physical_defect_mode_bound (η θ κ ε d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ<1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 0).basis (G 0).probability
        (BKM.center (G 0).basis (G 0).probability
          (rawFirstSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 1) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 0*(h (outputReference η θ a d)/h (a 0))*
        BKM.quadratic G0.basis G0.probability Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 1).basis (G 1).probability
        (BKM.center (G 1).basis (G 1).probability
          (rawSecondSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 1*(h (outputReference η θ a d)/h (a 1))*
        BKM.quadratic G0.basis G0.probability Z)
    (hr : (1+ε)*(∑ i, twoPortLambda η θ i*a i) ≤ outputReference η θ a d)
    (hs : (1+ε)*(∑ i, twoPortLambda η θ i*(a i+1)) ≤ outputReference η θ a d+1)
    (j : Fin n) :
    ‖G0.defect (outputReference η θ a d) hr0 j‖ ≤
      Real.sqrt (∑ i, ((1-κ)*twoPortLambda η θ i)*‖(G i).defect (a i) (ha i) j‖^2)+
      Real.sqrt ((1-κ)*κ)*‖V.weakMean (outputReference η θ a d) j‖*
        mixtureConstant (outputReference η θ a d) := by sorry
