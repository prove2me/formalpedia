-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_minimum_physical_pairing_balance
-- name    : OAI.EntropyPhotonNumber.Regularization.minimum_physical_pairing_balance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:43:31.196454+00:00
-- url     : https://prove2.me/theorems/92c36f13-eca7-43f9-b1ee-b7026b8b06d0
-- title:
--   Generator pairing balance and Hessian bounds at a minimizer of the regularized two-input problem
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, total number $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, and the diagonal weight $\hat N=1+\sum_ja_j^\dagger a_j$, i.e. $\hat N|k\rangle=(1+|k|)|k\rangle$. A state is a positive bounded operator on $F$ whose number-basis diagonal sums to $1$. For a state $\rho$ write $S(\rho)=-\operatorname{Tr}\rho\log\rho$, $E(\rho)=\sum_k|k|\,\rho_{kk}$ and $M_4(\rho)=\sum_k(1+|k|)^4\rho_{kk}$; $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$.
--
--   *Regularized problem.* Fix $\eta,\delta,\kappa\in[0,1]$, finite-energy states $\tau_D,\tau_0$ and constants $c,a_1,a_2,b_1,b_2,\zeta>0$. For states $\rho,\sigma$ let $\mathcal B_\theta(\cdot,\cdot)$ denote the beam-splitter output at transmissivity $\theta$ and put
--   $$\omega(\rho,\sigma)=(1-\kappa)\,\mathcal B_{1-\delta}\bigl(\mathcal B_\eta(\rho,\sigma),\tau_D\bigr)+\kappa\,\tau_0,$$
--   $$\Phi(\rho,\sigma)=c\,S(\omega(\rho,\sigma))-a_1S(\rho)-a_2S(\sigma)+b_1E(\rho)+\zeta M_4(\rho)+b_2E(\sigma)+\zeta M_4(\sigma).$$
--   Let $\mathcal F_1$ be the channel $\rho'\mapsto\mathcal B_{1-\delta}(\mathcal B_\eta(\rho',\sigma),\tau_D)$ and $\mathcal F_2$ the channel $\sigma'\mapsto\mathcal B_{1-\delta}(\mathcal B_\eta(\rho,\sigma'),\tau_D)$, with Heisenberg duals $\mathcal F_1^*,\mathcal F_2^*$.
--
--   A *Gibbs representation of $\rho$ with quartic coefficient $k$* consists of a positive bounded operator $B_\rho$, a Hilbert basis $(g_j)_{j}$ of $F$ and numbers $u_j>0$ with $\mathcal Z=\sum_je^{-u_j}<\infty$ such that $\hat N^{-2}\bigl(k+\hat N^{-3/2}B_\rho\hat N^{-3/2}\bigr)^{-1}\hat N^{-2}g_j=u_j^{-1}g_j$ for all $j$ and $\rho=\sum_j\frac{e^{-u_j}}{\mathcal Z}|g_j\rangle\langle g_j|$ (moreover $\rho$ is injective and has finite seventh moment). Formally $\rho=e^{-H}/\mathcal Z$ with $H=k\hat N^4+\hat N^{1/2}B_\rho\hat N^{1/2}$. Its *quartic logarithm* is the bounded operator
--   $$\mathcal L_\rho=k\,\mathrm{Id}+\hat N^{-3/2}B_\rho\hat N^{-3/2}+(\log\mathcal Z)\,\hat N^{-4},$$
--   formally $\hat N^{-2}(-\log\rho)\hat N^{-2}$.
--
--   For a state $\mu$, a *weighted column family* of $\mu$ is a family $x=(x_l)_l$ in $F$ with $\sum_l\|x_l\|^2<\infty$ such that $y_l=\hat N^{-3}x_l$ satisfy $\sum_l\|y_l\|^2=1$ and $\sum_l|y_l\rangle\langle y_l|=\mu$. For $s\in\mathbb{R}$ and a bounded operator $Z$, the *generator pairing* is
--   $$\Gamma_s(x;Z)=\sum_{j=1}^n\sum_l\Bigl[(s+1)\Bigl(\langle\hat N^2a_jy_l,Z\hat N^2a_jy_l\rangle-\tfrac12\langle\hat N^2y_l,Z\hat N^2\hat n_jy_l\rangle-\tfrac12\langle\hat N^2\hat n_jy_l,Z\hat N^2y_l\rangle\Bigr)+s\Bigl(\langle\hat N^2a_j^\dagger y_l,Z\hat N^2a_j^\dagger y_l\rangle-\tfrac12\langle\hat N^2y_l,Z\hat N^2(\hat n_j+1)y_l\rangle-\tfrac12\langle\hat N^2(\hat n_j+1)y_l,Z\hat N^2y_l\rangle\Bigr)\Bigr]$$
--   with $\hat n_j=a_j^\dagger a_j$ (all vectors lie in $F$ because $\hat N^{2}a_j\hat N^{-3}$ etc. are bounded). Formally $\Gamma_s(x;Z)=\operatorname{Tr}\mu\,\mathcal L_s^*(\hat N^2Z\hat N^2)$, where $\mathcal L_s^*(K)=\sum_j(s+1)(a_j^\dagger Ka_j-\frac12\{\hat n_j,K\})+s(a_jKa_j^\dagger-\frac12\{a_ja_j^\dagger,K\})$ is the Heisenberg generator of the thermal-noise semigroup with mean photon number $s$.
--
--   For $\theta\in[0,1]$, a state $\nu$ with finite fourth moment and a bounded $T$, let $\mathcal C^{\theta}_{\nu}(T)$ and $\mathcal C'^{\theta}_{\nu}(T)$ be the weighted conditional operators: with $U_\theta$ the passive beam-splitter unitary of transmissivity $\theta$ on $\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$, they are defined by
--   $$\mathcal C^\theta_\nu(T)=\hat N^{-2}\,\Psi^{*}_{\theta,\nu}\bigl(\hat N^{2}T\hat N^{2}\bigr)\,\hat N^{-2},\qquad \langle x,\Psi^*_{\theta,\nu}(K)x'\rangle=\sum_m\bigl\langle U_\theta(x\otimes\sqrt\nu|m\rangle),(K\otimes\mathrm{Id})\,U_\theta(x'\otimes\sqrt\nu|m\rangle)\bigr\rangle ,$$
--   and likewise $\mathcal C'^\theta_\nu$ with $\sqrt\nu|m\rangle\otimes x$ (the known state in the first port). (In the file these are written with bounded weight ratios, as $\sum_mW_m^*(T\otimes\mathrm{Id})W_m$ for bounded $W_m$, so they are bounded operators; the displayed formula is their meaning.)
--
--   For a basis $(e_j)$ and weights $w_j$ put $Q_{e,w}(T)=\sum_{i,j}L(w_i,w_j)|\langle e_i,Te_j\rangle|^2$ ($L$ the logarithmic mean), $\mathrm c_{e,w}(T)=T-(\sum_jw_j\langle e_j,Te_j\rangle)\mathrm{Id}$, and let $\mathcal Z(e,w)$ be the span of the operators $|e_i\rangle\langle e_j|-\delta_{ij}w_i\mathrm{Id}$.
--
--   **Theorem.** Assume $\rho,\sigma,\tau_D$ have finite fourth moments, $\tau_0=\tau_r$ is the thermal state with mean $r>0$ per mode, $\kappa>0$, and $(\rho,\sigma)$ minimizes $\Phi$ over all pairs of states with finite fourth moments. Then there exist a Hilbert basis $(b_j)_{j\in J}$ and $p_j>0$ with $\sum_jp_j=1$ and $\omega(\rho,\sigma)b_j=p_jb_j$; Gibbs representations $G_1$ of $\rho$ (quartic coefficient $\zeta/a_1$, quartic logarithm $\mathcal L_\rho$, eigenbasis $g^{(1)}$, weights $w^{(1)}$) and $G_2$ of $\sigma$ (coefficient $\zeta/a_2$, $\mathcal L_\sigma$, $g^{(2)}$, $w^{(2)}$); and positive bounded operators $B,D_1,D_2$ with
--   $$\langle x,Bx\rangle=\sum_j(-\log p_j)|\langle b_j,\hat N^{-2}x\rangle|^2,\qquad\langle x,D_ix\rangle=\sum_k|k|\,|(\hat N^{-2}x)_k|^2$$
--   (in $[0,\infty]$), such that:
--
--   1. for all $s_1,s_2\in\mathbb{R}$, every weighted column family $x$ of $\rho$ and every weighted column family $y$ of $\sigma$,
--   $$a_1\Gamma_{s_1}(x;\mathcal L_\rho)+a_2\Gamma_{s_2}(y;\mathcal L_\sigma)=c(1-\kappa)\Bigl[\Gamma_{s_1}\bigl(x;\mathcal C^\eta_\sigma\mathcal C^{1-\delta}_{\tau_D}B\bigr)+\Gamma_{s_2}\bigl(y;\mathcal C'^\eta_\rho\mathcal C^{1-\delta}_{\tau_D}B\bigr)\Bigr]+b_1\Gamma_{s_1}(x;D_1)+b_2\Gamma_{s_2}(y;D_2)+\zeta\bigl(\Gamma_{s_1}(x;\mathrm{Id})+\Gamma_{s_2}(y;\mathrm{Id})\bigr);$$
--   2. for all $Z\in\mathcal Z(b,p)$: $(1-\kappa)^2\,Q_{g^{(1)},w^{(1)}}\bigl(\mathrm c_{g^{(1)},w^{(1)}}(\mathcal F_1^*Z)\bigr)\le\frac{a_1}{c}\,Q_{b,p}(Z)$;
--   3. for all $Z\in\mathcal Z(b,p)$: $(1-\kappa)^2\,Q_{g^{(2)},w^{(2)}}\bigl(\mathrm c_{g^{(2)},w^{(2)}}(\mathcal F_2^*Z)\bigr)\le\frac{a_2}{c}\,Q_{b,p}(Z)$.
--
--   Formally $B=\hat N^{-2}(-\log\omega)\hat N^{-2}$, so item 1 says that the first-order optimality conditions for $\rho$ and $\sigma$, paired with the thermal relaxation generators, balance exactly; items 2 and 3 are the second-order conditions in the logarithmic-mean metric. These are the two inputs of the stationarity argument for the minimizers.
--
--   **Formalization Note** The data $(\eta,\delta,\kappa,\tau_D,\tau_0,c,a_i,b_i,\zeta)$ form the structure `Regularization n`; $\omega$ is `R.output`, $\Phi$ is `R.objective`, $\Gamma_s$ is `WeightedGenerator.pairing`, $\mathcal C$ and $\mathcal C'$ are `weightedConditional` and `weightedConditionalRight` applied to `weightedRoot 2` (the columns $\hat N^2\sqrt\nu|m\rangle$), and $\mathcal F_1^*,\mathcal F_2^*$ are the duals of `R.firstFlow σ`, `R.secondFlow ρ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/PhysicalMinimum.lean#L648-L704

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Regularization
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} (R : Regularization n)

theorem OAI.EntropyPhotonNumber.Regularization.minimum_physical_pairing_balance (ρ σ : State n) (hmρ : FiniteMoment 4 ρ)
    (hmσ : FiniteMoment 4 σ) (hmD : FiniteMoment 4 R.τD)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
        (B D1 D2 : Fock n →L[ℂ] Fock n), B.IsPositive ∧ D1.IsPositive ∧ D2.IsPositive ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
          basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D1 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D2 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ (s1 s2 : ℝ) (X : WeightedColumns ρ) (Y : WeightedColumns σ),
          (R.a1:ℂ)*WeightedGenerator.pairing s1 X.vector G1.quarticLogarithm+
          (R.a2:ℂ)*WeightedGenerator.pairing s2 Y.vector G2.quarticLogarithm=
          (R.c:ℂ)*((1-R.κ:ℝ):ℂ)*
            (WeightedGenerator.pairing s1 X.vector
              (weightedConditional R.η R.hη (weightedRoot 2 σ hmσ)
                (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                  (weightedRoot 2 R.τD hmD) B))+
             WeightedGenerator.pairing s2 Y.vector
              (weightedConditionalRight R.η R.hη (weightedRoot 2 ρ hmρ)
                (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                  (weightedRoot 2 R.τD hmD) B)))+
          (R.b1:ℂ)*WeightedGenerator.pairing s1 X.vector D1+
          (R.b2:ℂ)*WeightedGenerator.pairing s2 Y.vector D2+
          (R.ζ:ℂ)*(WeightedGenerator.pairing s1 X.vector (1 : Fock n →L[ℂ] Fock n)+
            WeightedGenerator.pairing s2 Y.vector (1 : Fock n →L[ℂ] Fock n))) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G1.basis (gibbsWeight G1.eigenval)
            (BKM.center G1.basis (gibbsWeight G1.eigenval)
              ((R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).dual Z)) ≤
            (R.a1/R.c)*BKM.quadratic b p Z) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G2.basis (gibbsWeight G2.eigenval)
            (BKM.center G2.basis (gibbsWeight G2.eigenval)
              ((R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).dual Z)) ≤
            (R.a2/R.c)*BKM.quadratic b p Z) := by sorry
