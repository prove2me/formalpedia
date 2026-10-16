-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_physical_defect_convolution
-- name    : OAI.EntropyPhotonNumber.physical_defect_convolution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:51:09.656274+00:00
-- url     : https://prove2.me/theorems/a7a6d6dc-245f-493a-a5ce-0a9907c53ca5
-- title:
--   Convolution identity for thermal-balance defects through a two-stage beam splitter
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
--   so that $\Delta^{G,t}_j(\mathrm{obs}(Z))=\sum_{l,m}d_{lm}\overline{c_{lm}}\langle b_l,Zb_m\rangle$ is a weak form of the thermal balance $(t+1)a_j$ versus $t\,a_j^\dagger$.
--
--   **Setting.** Let $\eta,\theta\in(0,1)$, $\kappa\in[0,1]$, $d>0$, $a_0,a_1>0$. Let $\rho_0,\rho_1,\tau_D,m,\gamma,\omega,\rho^\circ$ be states with $m=\mathcal B_\eta(\rho_0,\rho_1)$ and $\gamma=\mathcal B_\theta(m,\tau_D)$, both in the number-basis sense of the beam-splitter output relation. For $\eta\in[0,1]$ and states $\rho_0,\rho_1$, write $\mathcal B_\eta(\rho_0,\rho_1)$ for the beam-splitter output (the reduced state of the retained port after the passive rotation of transmissivity $\eta$ in every mode applied to $\rho_0\otimes\rho_1$). Put $\lambda_0=\theta\eta$, $\lambda_1=\theta(1-\eta)$ and $r_0=\theta(\eta a_0+(1-\eta)a_1)+(1-\theta)d$. For a bounded $Z$ let $A_0(Z)$ be the partial expectation, over the second input in state $\rho_1$, of the Heisenberg dual of the two-stage map (mix the two inputs at $\eta$, then mix the result with $\tau_D$ at $\theta$, keep the retained port) applied to $Z$, and $A_1(Z)$ the analogous partial expectation over the first input in state $\rho_0$. With $\mathrm c_i(T)=T-(\sum_lp^{(i)}_l\langle b^{(i)}_l,Tb^{(i)}_l\rangle)\mathrm{Id}$ the centering in the eigenbasis of $\rho_i$, the normalized slices are $N_i(Z)=\lambda_i^{-1/2}\,\mathrm c_i(A_iZ)$. Assume $r_0>0$, that $\tau_D$ and $\omega$ are the number-diagonal thermal states with mean photon numbers $d$ and $r_0$ per mode, and that $\rho^\circ=(1-\kappa)\gamma+\kappa\omega$. Let $G_0,G_1$ be spectral logarithm data for $\rho_0,\rho_1$, $G^\circ$ one for $\rho^\circ$, and let $y^{V}=(\hat N^{-3}v_l)$ and $y^{O}=(\hat N^{-3}o_l)$ come from weighted column families $v$ of $\gamma$ and $o$ of $\omega$ (weighted column families of $\tau_D$ and $m$ are also given).
--
--   **Theorem.** For every mode $j$ and every bounded operator $Z$ on $F$,
--   $$\Delta^{G^\circ,r_0}_j\bigl(\mathrm{obs}_{\mathcal S_{G^\circ}(r_0)}Z\bigr)=\sum_{i=0}^{1}(1-\kappa)\lambda_i\,\Delta^{G_i,a_i}_j\bigl(\mathrm{obs}_{\mathcal S_{G_i}(a_i)}(N_iZ)\bigr)+\sqrt{(1-\kappa)\kappa}\;\overline W\;\mathcal M(Z),$$
--   where $\overline W=(r_0+1)\sum_l\langle a_jy^V_l,y^V_l\rangle-r_0\sum_l\langle y^V_l,a_j^\dagger y^V_l\rangle$ is the weak mean of $\gamma$ in mode $j$ and $\mathcal M(Z)=\sqrt{(1-\kappa)\kappa}\,\bigl(\sum_l\langle y^V_l,Zy^V_l\rangle-\sum_l\langle y^O_l,Zy^O_l\rangle\bigr)$.
--
--   The output defect functional is thus a weighted sum ("convolution") of the two input defect functionals composed with the normalized conditional slices of the beam-splitter dual, plus an explicit error from replacing a fraction $\kappa$ of the output by a thermal state.
--
--   **Formalization Note** $\Delta^{G,t}_j$ is `G.ambientDefect t ht j`, $\mathrm{obs}$ is `(G.thermalSpace t ht).observable`, $N_i$ is `normalizedSlices … (twoPortLambda η θ) i`, $r_0$ is `outputReference η θ a d`, $\overline W$ is `V.weakMean r₀ j`, and $\mathcal M$ is `EnsembleL2.mixtureFunctional … (1-κ)`. The beam-splitter relations are `IsBeamSplitterOutput`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L41-L101

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
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

theorem OAI.EntropyPhotonNumber.physical_defect_convolution (η θ κ d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    G0.ambientDefect (outputReference η θ a d) hr0 j
        ((G0.thermalSpace (outputReference η θ a d) hr0).observable Z)=
      (∑ i, (((1-κ)*twoPortLambda η θ i:ℝ):ℂ)*
        (G i).ambientDefect (a i) (ha i) j ((G i).thermalSpace (a i) (ha i) |>.observable
          (normalizedSlices η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) (ρ 1) τD
            (fun i => (G i).thermalSpace (a i) (ha i)) (twoPortLambda η θ) i Z)))+
      ((Real.sqrt ((1-κ)*κ):ℂ)*V.weakMean (outputReference η θ a d) j)*
        EnsembleL2.mixtureFunctional (fun k => inverseWeight 3 (V.vector k))
          (fun k => inverseWeight 3 (O.vector k)) V.normalized.summable O.normalized.summable (1-κ) Z := by sorry
