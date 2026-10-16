-- Prove2me | Theorems.Thm_OAI_ThermalDual_dual_bound_from_core
-- name    : OAI.ThermalDual.dual_bound_from_core
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:48:45.629665+00:00
-- url     : https://prove2.me/theorems/ba613ab9-69af-48d4-b285-f3621d4ec81f
-- title:
--   Norm bound for a functional on the centered space from an operator-level decomposition
-- statement:
--   Put $h(r)=\log(r+1)-\log r$ for $r>0$, let $L$ be the logarithmic mean ($L(x,y)=\frac{y-x}{\log y-\log x}$, $L(x,x)=x$), $f(x)=x/\sinh x$ ($f(0)=1$), and let
--   $$w(r,\nu)=\frac1{h(r)}\,\frac{f(h(r)\nu/2)\,f(-h(r)/2)}{f(h(r)\nu/2-h(r)/2)}$$
--   be the thermal weight. A *thermal spectral datum* $\mathcal S=(e,p,r)$ on a complex Hilbert space $E$ is a Hilbert basis $(e_k)_{k\in I}$, weights $p_k>0$ with $\sum_kp_k=1$, and $r>0$; put $\nu_{kl}=(\log p_k-\log p_l)/h(r)$ and $m_{kl}=h(r)\,L(p_k,p_l)\,w(r,\nu_{kl})>0$. Its *observable map* sends a bounded operator $Z$ to
--   $$\mathrm{obs}_{\mathcal S}(Z)=\Bigl(\sqrt{m_{kl}}\,\langle e_k,Ze_l\rangle\Bigr)_{k,l}\in\ell^2(I\times I),$$
--   so that $\|\mathrm{obs}_{\mathcal S}(Z)\|^2=Q^{\mathcal S}_w(Z):=\sum_{k,l}m_{kl}|\langle e_k,Ze_l\rangle|^2$. The *centered space* $\mathcal C(\mathcal S)\subseteq\ell^2(I\times I)$ is the orthogonal complement of $\mathrm{obs}_{\mathcal S}(\mathrm{Id})$ (the vector with diagonal entries $\sqrt{p_k}$ and zero off-diagonal entries), and $\mathcal Z(\mathcal S)$ is the span of the operators $|e_k\rangle\langle e_l|-\delta_{kl}p_k\mathrm{Id}$. Finally let $w_*(r)=\inf_{\nu\in\mathbb{R}}w(r,\nu)$ (which is $\ge r>0$) and $\chi(r)=\bigl(h(r)\,w_*(r)\bigr)^{-1/2}$.
--
--   For square-summable families $v=(v_i)$, $u=(u_l)$ in $E$ and $t\in[0,1]$ define the *mixture functional* on bounded operators
--   $$\mathcal M_{v,u,t}(Z)=\sqrt{t(1-t)}\Bigl(\sum_i\langle v_i,Zv_i\rangle-\sum_l\langle u_l,Zu_l\rangle\Bigr).$$
--
--   **Theorem.** Let $\mathcal S_0$ and $\mathcal S_i$ ($i\in K$, $K$ finite) be thermal spectral data on a complex Hilbert space $E$, let $w_i\ge0$, let $L_i$ be complex-linear maps on bounded operators, let $q_0$ be a continuous linear functional on $\ell^2(I_0\times I_0)$ and $q_i$ continuous linear functionals on $\ell^2(I_i\times I_i)$. Let $v,u$ be families with $\sum_i\|v_i\|^2=1=\sum_l\|u_l\|^2$, let $t\in[0,1]$, and assume that the ensemble of $\mathcal S_0$ represents the mixture:
--   $$\sum_kp^{(0)}_k|e^{(0)}_k\rangle\langle e^{(0)}_k|=t\sum_i|v_i\rangle\langle v_i|+(1-t)\sum_l|u_l\rangle\langle u_l| .$$
--   Let $c\in\mathbb{C}$ and suppose that for every $Z\in\mathcal Z(\mathcal S_0)$
--   $$\sum_iw_i\,Q^{\mathcal S_i}_w(L_iZ)\le Q^{\mathcal S_0}_w(Z)\quad\text{and}\quad q_0\bigl(\mathrm{obs}_{\mathcal S_0}Z\bigr)=\sum_iw_i\,q_i\bigl(\mathrm{obs}_{\mathcal S_i}(L_iZ)\bigr)+c\,\mathcal M_{v,u,t}(Z).$$
--   Then the restriction of $q_0$ to the centered space satisfies
--   $$\bigl\|q_0|_{\mathcal C(\mathcal S_0)}\bigr\|\le\sqrt{\sum_iw_i\|q_i\|^2}+|c|\,\chi(r_0).$$
--
--   This is the duality step of the metric argument: a contraction of the thermal quadratic forms together with a decomposition of the functional $q_0$ through the maps $L_i$ (plus a mixing term) bounds the dual norm of $q_0$ by the dual norms of the $q_i$.
--
--   **Formalization Note** $\|q_0|_{\mathcal C}\|$ is the operator norm of `q₀.comp (centeredSpace …).subtypeL`; $\mathrm{obs}$ is `Space.observable`, $Q^{\mathcal S}_w$ is `Space.pquad thermalWeight`, $\mathcal M$ is `EnsembleL2.mixtureFunctional`, $\chi$ is `mixtureConstant`, and the mixture hypothesis uses the ensemble $(\sqrt{p_k}e_k)$ and `EnsembleL2.mixture`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Duality.lean#L421-L456

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

open OAI
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

theorem OAI.ThermalDual.dual_bound_from_core (S₀ : Space E) (S : K → Space E)
    (w : K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : (i : K) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (q₀ : lp (fun _ : S₀.I × S₀.I => ℂ) 2 →L[ℂ] ℂ)
    (q : (i : K) → lp (fun _ : (S i).I × (S i).I => ℂ) 2 →L[ℂ] ℂ)
    (v : I → E) (u : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hu : HasSum (fun j => ‖u j‖^2) 1)
    (he : TraceEnsemble.operator S₀.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v u t))
    (c : ℂ)
    (hL : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      ∑ i, w i*(S i).pquad thermalWeight (L i Z) ≤ S₀.pquad thermalWeight Z)
    (hq : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      q₀ (S₀.observable Z) = (∑ i, (w i:ℂ)*q i ((S i).observable (L i Z)))+
        c*EnsembleL2.mixtureFunctional v u hv.summable hu.summable t Z) :
    ‖q₀.comp (centeredSpace S₀.r S₀.rpos S₀.p S₀.pos S₀.sum.summable).subtypeL‖ ≤
      Real.sqrt (∑ i, w i*‖q i‖^2)+‖c‖*mixtureConstant S₀.r := by sorry
