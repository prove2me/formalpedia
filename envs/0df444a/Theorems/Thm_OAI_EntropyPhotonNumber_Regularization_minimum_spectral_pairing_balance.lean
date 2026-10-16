-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_minimum_spectral_pairing_balance
-- name    : OAI.EntropyPhotonNumber.Regularization.minimum_spectral_pairing_balance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:59:04.406602+00:00
-- url     : https://prove2.me/theorems/53b6d427-cac0-43c2-9327-a9fd552d7238
-- title:
--   Spectral pairing balance at a minimizer with thermal environment and thermal replacement
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)$, $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, $\hat n_j=a_j^\dagger a_j$, and the diagonal weight $\hat N=1+\sum_j\hat n_j$ (so $\hat N|k\rangle=(1+|k|)|k\rangle$). States are positive operators on $F$ with number-basis diagonal summing to $1$; $E(\rho)=\sum_k|k|\rho_{kk}$, and $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$. For $r>0$, $\tau_r$ denotes the thermal state with mean photon number $r$ per mode, $\langle k|\tau_r|l\rangle=\delta_{kl}\prod_i\frac1{r+1}(\frac r{r+1})^{k_i}$, and $h(r)=\log(r+1)-\log r$.
--
--   *Regularized problem.* Fix $\eta,\delta,\kappa\in[0,1]$, finite-energy states $\tau_D,\tau_0$ and constants $c,a_1,a_2,b_1,b_2,\zeta>0$. With $\mathcal B_\theta$ the beam-splitter output at transmissivity $\theta$, put
--   $$\omega(\rho,\sigma)=(1-\kappa)\,\mathcal B_{1-\delta}\bigl(\mathcal B_\eta(\rho,\sigma),\tau_D\bigr)+\kappa\tau_0,\qquad \Phi(\rho,\sigma)=cS(\omega)-a_1S(\rho)-a_2S(\sigma)+b_1E(\rho)+\zeta M_4(\rho)+b_2E(\sigma)+\zeta M_4(\sigma),$$
--   with $S$ the von Neumann entropy and $M_4(\rho)=\sum_k(1+|k|)^4\rho_{kk}$.
--
--   A *Gibbs representation of $\rho$ with quartic coefficient $k$* consists of a positive bounded $B_\rho$, a Hilbert basis $(g_j)$ and numbers $u_j>0$ with $\mathcal Z=\sum_je^{-u_j}<\infty$ such that $\hat N^{-2}(k+\hat N^{-3/2}B_\rho\hat N^{-3/2})^{-1}\hat N^{-2}g_j=u_j^{-1}g_j$ and $\rho=\sum_j\frac{e^{-u_j}}{\mathcal Z}|g_j\rangle\langle g_j|$ ($\rho$ injective with finite seventh moment); its probabilities are $e^{-u_j}/\mathcal Z$ and its log sandwich is $\mathcal L_\rho=k+\hat N^{-3/2}B_\rho\hat N^{-3/2}+(\log\mathcal Z)\hat N^{-4}$ (formally $\hat N^{-2}(-\log\rho)\hat N^{-2}$).
--
--   A *spectral logarithm datum* for a state $\rho$ consists of a Hilbert basis $(b_j)_{j\in J}$ of $F$ and $p_j>0$ with $\sum_jp_j=1$ and $\rho b_j=p_jb_j$; spectral columns $x_j\in F$ with $\sum_j\|x_j\|^2<\infty$ and $\hat N^{-3}x_j=\sqrt{p_j}\,b_j$; and a bounded symmetric operator $\mathcal L$ (the log sandwich) with
--   $$\operatorname{Re}\langle y,\mathcal Ly\rangle=\sum_j(-\log p_j)\,\bigl|\langle b_j,\hat N^{-2}y\rangle\bigr|^2\quad(y\in F),\qquad \mathcal L(\hat N^{-1}x_j)=(-\log p_j)\,\hat N^{-5}x_j .$$
--   Formally $\mathcal L=\hat N^{-2}(-\log\rho)\hat N^{-2}$.
--
--   For a state $\mu$ with finite sixth moment, its canonical columns are $x^\mu_k=\hat N^3\sqrt\mu|k\rangle$, with $y_k=\hat N^{-3}x^\mu_k=\sqrt\mu|k\rangle$. For $s\in\mathbb{R}$ and a bounded $Z$ the *generator pairing* is
--   $$\Gamma_s(x^\mu;Z)=\sum_{j=1}^n\sum_k\Bigl[(s+1)\Bigl(\langle\hat N^2a_jy_k,Z\hat N^2a_jy_k\rangle-\tfrac12\langle\hat N^2y_k,Z\hat N^2\hat n_jy_k\rangle-\tfrac12\langle\hat N^2\hat n_jy_k,Z\hat N^2y_k\rangle\Bigr)+s\Bigl(\langle\hat N^2a_j^\dagger y_k,Z\hat N^2a_j^\dagger y_k\rangle-\tfrac12\langle\hat N^2y_k,Z\hat N^2(\hat n_j+1)y_k\rangle-\tfrac12\langle\hat N^2(\hat n_j+1)y_k,Z\hat N^2y_k\rangle\Bigr)\Bigr],$$
--   formally $\operatorname{Tr}\mu\,\mathcal L_s^*(\hat N^2Z\hat N^2)$ with $\mathcal L_s^*(K)=\sum_j(s+1)(a_j^\dagger Ka_j-\frac12\{\hat n_j,K\})+s(a_jKa_j^\dagger-\frac12\{a_ja_j^\dagger,K\})$ the Heisenberg generator of the thermal-noise semigroup with mean photon number $s$.
--
--   Let $\mathcal N=\hat N^{-2}\Bigl(\sum_j\hat n_j\Bigr)\hat N^{-2}$ (the diagonal operator with entries $|k|/(1+|k|)^4$). For a basis $e$ and weights $w$ let $Q_{e,w}(T)=\sum_{i,l}L(w_i,w_l)|\langle e_i,Te_l\rangle|^2$ ($L$ the logarithmic mean), $\mathrm c_{e,w}(T)=T-(\sum_iw_i\langle e_i,Te_i\rangle)\mathrm{Id}$, and $\mathcal Z(e,w)$ the span of $|e_i\rangle\langle e_l|-\delta_{il}w_i\mathrm{Id}$. Let $A_1(Z)$ be the partial expectation over the second input in state $\sigma$ of the Heisenberg dual of $\rho'\otimes\sigma'\mapsto\mathcal B_{1-\delta}(\mathcal B_\eta(\rho',\sigma'),\tau_D)$ applied to $Z$, and $A_2(Z)$ the partial expectation over the first input in state $\rho$.
--
--   **Theorem.** Let $\rho,\sigma$ have finite fourth moments, let $s_1,s_2,d,r_0\in\mathbb{R}$ with $d>0$, $r_0>0$ and
--   $$r_0=(1-\delta)\bigl(\eta s_1+(1-\eta)s_2\bigr)+\delta d,$$
--   assume $\tau_D=\tau_d$, $\tau_0=\tau_{r_0}$, $\kappa>0$, and that $(\rho,\sigma)$ minimizes $\Phi$ among all pairs of states with finite fourth moments. Then $\rho,\sigma$ and $\omega=\omega(\rho,\sigma)$ have finite sixth moments, and there are Gibbs representations $G_1$ of $\rho$ (coefficient $\zeta/a_1$; basis $g^{(1)}$, probabilities $w^{(1)}$, log sandwich $\mathcal L_\rho$), $G_2$ of $\sigma$ (coefficient $\zeta/a_2$; $g^{(2)}$, $w^{(2)}$, $\mathcal L_\sigma$) and a spectral logarithm datum $G_0$ of $\omega$ (basis $b$, probabilities $p$, log sandwich $\mathcal L_\omega$) such that
--
--   1. $a_1\Gamma_{s_1}(x^\rho;\mathcal L_\rho)+a_2\Gamma_{s_2}(x^\sigma;\mathcal L_\sigma)=c\,\Gamma_{r_0}(x^\omega;\mathcal L_\omega)+b_1\Gamma_{s_1}(x^\rho;\mathcal N)+b_2\Gamma_{s_2}(x^\sigma;\mathcal N)+\zeta\bigl(\Gamma_{s_1}(x^\rho;\mathrm{Id})+\Gamma_{s_2}(x^\sigma;\mathrm{Id})\bigr)$;
--   2. for all $Z\in\mathcal Z(b,p)$: $(1-\kappa)^2\,Q_{g^{(1)},w^{(1)}}\bigl(\mathrm c_{g^{(1)},w^{(1)}}(A_1Z)\bigr)\le\frac{a_1}{c}\,Q_{b,p}(Z)$;
--   3. for all $Z\in\mathcal Z(b,p)$: $(1-\kappa)^2\,Q_{g^{(2)},w^{(2)}}\bigl(\mathrm c_{g^{(2)},w^{(2)}}(A_2Z)\bigr)\le\frac{a_2}{c}\,Q_{b,p}(Z)$.
--
--   Formally item 1 reads $a_1\operatorname{Tr}\rho\,\mathcal L^*_{s_1}(-\log\rho)+a_2\operatorname{Tr}\sigma\,\mathcal L^*_{s_2}(-\log\sigma)=c\operatorname{Tr}\omega\,\mathcal L^*_{r_0}(-\log\omega)+\dots$: when the environment and replacement states are thermal with compatible means, the output term collapses to a single thermal generator acting on the output. This is the stationarity identity in which the centered energy terms later cancel.
--
--   **Formalization Note** The data are the structure `Regularization n`; $\Gamma_s$ is `WeightedGenerator.pairing` with columns `weightedRoot 3`, $\mathcal N$ is `numberSandwich n`, $A_1,A_2$ are `rawFirstSlice R.η (1-R.δ) … σ R.τD` and `rawSecondSlice … ρ R.τD`. The moment proofs `h6ρ h6σ h60` are part of the existential conclusion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L1131-L1199

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Regularization
open scoped BigOperators ComplexConjugate
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

theorem OAI.EntropyPhotonNumber.Regularization.minimum_spectral_pairing_balance (ρ σ : State n)
    (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    (s1 s2 d r0 : ℝ) (hd : 0<d) (hr0 : 0<r0)
    (heq : r0=(1-R.δ)*(R.η*s1+(1-R.η)*s2)+(1-(1-R.δ))*d)
    (hD : R.τD=thermalState n d hd) (hτ : R.τ0=thermalState n r0 hr0)
    (hκ : 0<R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
      (G0 : SpectralLogData n (R.output ρ σ))
      (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ) (h60 : FiniteMoment 6 (R.output ρ σ)),
      (R.a1:ℂ)*WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) G1.logSandwich+
      (R.a2:ℂ)*WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) G2.logSandwich=
      (R.c:ℂ)*WeightedGenerator.pairing r0 (weightedRoot 3 (R.output ρ σ) h60) G0.logSandwich+
      (R.b1:ℂ)*WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) (numberSandwich n)+
      (R.b2:ℂ)*WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) (numberSandwich n)+
      (R.ζ:ℂ)*(WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) (1 : Fock n →L[ℂ] Fock n)+
        WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) (1 : Fock n →L[ℂ] Fock n)) ∧
      (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
        (1-R.κ)^2*BKM.quadratic G1.basis G1.probability
          (BKM.center G1.basis G1.probability
            (rawFirstSlice R.η (1-R.δ) R.hη R.attenuation_mem σ R.τD Z)) ≤
          (R.a1/R.c)*BKM.quadratic G0.basis G0.probability Z) ∧
      (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
        (1-R.κ)^2*BKM.quadratic G2.basis G2.probability
          (BKM.center G2.basis G2.probability
            (rawSecondSlice R.η (1-R.δ) R.hη R.attenuation_mem ρ R.τD Z)) ≤
          (R.a2/R.c)*BKM.quadratic G0.basis G0.probability Z) := by sorry
