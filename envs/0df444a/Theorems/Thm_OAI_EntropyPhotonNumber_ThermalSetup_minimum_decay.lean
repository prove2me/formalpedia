-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_ThermalSetup_minimum_decay
-- name    : OAI.EntropyPhotonNumber.ThermalSetup.minimum_decay
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-16T03:01:40.884759+00:00
-- url     : https://prove2.me/theorems/780dda3d-f911-4d78-a75c-85708c0c6be3
-- title:
--   Defects and means of regularized minimizers are $O(\zeta)$
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)$, $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, $\hat n_j=a_j^\dagger a_j$, and the diagonal weight $\hat N=1+\sum_j\hat n_j$ (so $\hat N|k\rangle=(1+|k|)|k\rangle$). States are positive operators on $F$ with number-basis diagonal summing to $1$; $E(\rho)=\sum_k|k|\rho_{kk}$, and $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$. For $r>0$, $\tau_r$ denotes the thermal state with mean photon number $r$ per mode, $\langle k|\tau_r|l\rangle=\delta_{kl}\prod_i\frac1{r+1}(\frac r{r+1})^{k_i}$, and $h(r)=\log(r+1)-\log r$.
--
--   *Thermal setup.* Fix $\eta,\theta,\kappa\in(0,1)$, $\varepsilon>0$, $d>0$, $r_1,r_2>0$, and put
--   $$r_0=\theta\bigl(\eta r_1+(1-\eta)r_2\bigr)+(1-\theta)d,\qquad w_1=(1-\kappa)\theta\eta,\qquad w_2=(1-\kappa)\theta(1-\eta).$$
--   Let $L$ be the logarithmic mean, $f(x)=x/\sinh x$, $w(r,\nu)=\frac{1}{h(r)}\frac{f(h(r)\nu/2)f(-h(r)/2)}{f(h(r)\nu/2-h(r)/2)}$ the thermal weight, $w_*(r)=\inf_\nu w(r,\nu)$ and $\chi(r)=(h(r)w_*(r))^{-1/2}$. The setup assumes the slack conditions
--   $$(1+\varepsilon)\bigl(\theta\eta r_1+\theta(1-\eta)r_2\bigr)\le r_0,\qquad(1+\varepsilon)\bigl(\theta\eta(r_1+1)+\theta(1-\eta)(r_2+1)\bigr)\le r_0+1,$$
--   and the smallness $\kappa\le\varepsilon^2/\bigl(4(\varepsilon+2)\chi(r_0)^2\bigr)$. For $\zeta>0$ the associated regularization uses transmissivities $\eta$ and $\theta$, environment $\tau_d$, replacement $\tau_{r_0}$ with weight $\kappa$, and constants $c=1/h(r_0)$, $a_i=(1+\varepsilon)w_i/h(r_i)$, $b_i=\varepsilon w_i$ and $\zeta$; its output is $\omega(\rho,\sigma)=(1-\kappa)\,\mathcal B_\theta(\mathcal B_\eta(\rho,\sigma),\tau_d)+\kappa\tau_{r_0}$ and its objective is $\Phi_\zeta(\rho,\sigma)=cS(\omega)-a_1S(\rho)-a_2S(\sigma)+b_1E(\rho)+\zeta M_4(\rho)+b_2E(\sigma)+\zeta M_4(\sigma)$.
--
--   For a state $\mu$ with finite sixth moment its canonical columns are $x^\mu_k=\hat N^3\sqrt\mu|k\rangle$, with $y_k=\hat N^{-3}x^\mu_k=\sqrt\mu|k\rangle$. For $s\in\mathbb{R}$ and a bounded $Z$ the *generator pairing* is
--   $$\Gamma_s(x^\mu;Z)=\sum_{j=1}^n\sum_k\Bigl[(s+1)\Bigl(\langle\hat N^2a_jy_k,Z\hat N^2a_jy_k\rangle-\tfrac12\langle\hat N^2y_k,Z\hat N^2\hat n_jy_k\rangle-\tfrac12\langle\hat N^2\hat n_jy_k,Z\hat N^2y_k\rangle\Bigr)+s\Bigl(\langle\hat N^2a_j^\dagger y_k,Z\hat N^2a_j^\dagger y_k\rangle-\tfrac12\langle\hat N^2y_k,Z\hat N^2(\hat n_j+1)y_k\rangle-\tfrac12\langle\hat N^2(\hat n_j+1)y_k,Z\hat N^2y_k\rangle\Bigr)\Bigr],$$
--   formally $\operatorname{Tr}\mu\,\mathcal L_s^*(\hat N^2Z\hat N^2)$ with $\mathcal L_s^*(K)=\sum_j(s+1)(a_j^\dagger Ka_j-\frac12\{\hat n_j,K\})+s(a_jKa_j^\dagger-\frac12\{a_ja_j^\dagger,K\})$ the Heisenberg generator of the thermal-noise semigroup with mean photon number $s$.
--
--   For a state $\rho$ with an eigen-decomposition $\rho g_l=v_lg_l$ ($v_l>0$, $\sum_lv_l=1$) and a mode $j$, let $\mu_j=\sum_lv_l\langle g_l,a_jg_l\rangle$, $c_{lm}=\langle g_l,(a_j-\mu_j)g_m\rangle$, and for $t>0$ let $\Delta_j^{t}$ be the defect functional $x\mapsto\sum_{l,m}\frac{(t+1)v_m-tv_l}{\sqrt{m_{lm}}}\overline{c_{lm}}\,x_{lm}$ with $m_{lm}=h(t)L(v_l,v_m)w(t,\frac{\log v_l-\log v_m}{h(t)})$, restricted to the orthogonal complement in $\ell^2$ of the vector with diagonal entries $\sqrt{v_l}$; $\|\Delta^t_j\|$ is its norm. Gibbs representations are as in the companion results: a positive bounded $B_\rho$, a basis $(g_l)$ and $u_l>0$ with $\sum e^{-u_l}<\infty$, $\hat N^{-2}(k+\hat N^{-3/2}B_\rho\hat N^{-3/2})^{-1}\hat N^{-2}g_l=u_l^{-1}g_l$ and $\rho=\sum_l\frac{e^{-u_l}}{\sum e^{-u}}|g_l\rangle\langle g_l|$.
--
--   **Theorem.** Let $C_1,C_2\in\mathbb{R}$ be such that for every state $\mu$ with finite sixth moment
--   $$\operatorname{Re}\Gamma_{r_1}(x^\mu;\mathrm{Id})\le C_1\qquad\text{and}\qquad\operatorname{Re}\Gamma_{r_2}(x^\mu;\mathrm{Id})\le C_2 .$$
--   Let $\zeta>0$ and let $(\rho,\sigma)$, both with finite fourth moments, minimize $\Phi_\zeta$ among all pairs of states with finite fourth moments. Then there are Gibbs representations $G_1$ of $\rho$ with quartic coefficient $\zeta/a_1$ and $G_2$ of $\sigma$ with coefficient $\zeta/a_2$ (eigenbases $g^{(i)}$, Gibbs weights $v^{(i)}$) such that, with the defects and means computed in these eigen-decompositions,
--   $$w_1\Bigl(\sum_{j}\bigl\|\Delta^{(1),r_1}_j\bigr\|^2+\sum_j|\mu^{(1)}_j|^2\Bigr)+w_2\Bigl(\sum_j\bigl\|\Delta^{(2),r_2}_j\bigr\|^2+\sum_j|\mu^{(2)}_j|^2\Bigr)\le\frac{2(C_1+C_2)}{\varepsilon}\,\zeta .$$
--
--   As the quartic penalty $\zeta\to0$, the thermal-balance defects and the annihilation means of the minimizers therefore vanish linearly in $\zeta$; this is what forces limits of minimizers to be thermal. The hypothesis on $C_1,C_2$ is a uniform upper bound on the drift of the quartic moment, formally $\operatorname{Tr}\mu\,\mathcal L^*_{r}(\hat N^4)$.
--
--   **Formalization Note** The data are `ThermalSetup` and `P.reg n ζ hζ`; the Gibbs representations are `GibbsData n (ζ/((1+P.ε)*P.w1/h P.r1)) ρ` etc., the defects are `G1.defect _ P.r1 P.hr1 j` and the means `G1.annihilationMean j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L1406-L1475

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

theorem OAI.EntropyPhotonNumber.ThermalSetup.minimum_decay (C1 C2 : ℝ)
    (hC1 : ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
      (WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C1)
    (hC2 : ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
      (WeightedGenerator.pairing P.r2 (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C2)
    (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
      (P.reg n ζ hζ).objective ρ σ≤(P.reg n ζ hζ).objective ρ' σ') :
    ∃ (G1 : GibbsData n (ζ/((1+P.ε)*P.w1/h P.r1)) ρ)
      (G2 : GibbsData n (ζ/((1+P.ε)*P.w2/h P.r2)) σ),
      P.w1*((∑ j, ‖G1.defect (div_pos hζ (P.reg n ζ hζ).ha1) P.r1 P.hr1 j‖^2)+
        (∑ j, ‖G1.annihilationMean j‖^2))+
      P.w2*((∑ j, ‖G2.defect (div_pos hζ (P.reg n ζ hζ).ha2) P.r2 P.hr2 j‖^2)+
        (∑ j, ‖G2.annihilationMean j‖^2)) ≤ (2*(C1+C2)/P.ε)*ζ := by sorry
