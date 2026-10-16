-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_canonical_output_generator
-- name    : OAI.EntropyPhotonNumber.Regularization.canonical_output_generator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:44:31.410351+00:00
-- url     : https://prove2.me/theorems/71f65b87-2ba4-41d1-b48d-222fbe2c5b0e
-- title:
--   Thermal generator on the regularized beam-splitter output splits into the input generators
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, total number $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, and the diagonal weight $\hat N=1+\sum_ja_j^\dagger a_j$, i.e. $\hat N|k\rangle=(1+|k|)|k\rangle$. A state is a positive bounded operator on $F$ whose number-basis diagonal sums to $1$. For a state $\rho$ write $S(\rho)=-\operatorname{Tr}\rho\log\rho$, $E(\rho)=\sum_k|k|\,\rho_{kk}$ and $M_4(\rho)=\sum_k(1+|k|)^4\rho_{kk}$; $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$.
--
--   Fix $\eta,\delta,\kappa\in[0,1]$ and states $\tau_D,\tau_0$, and for states $\rho,\sigma$ put
--   $$\omega(\rho,\sigma)=(1-\kappa)\,\mathcal B_{1-\delta}\bigl(\mathcal B_\eta(\rho,\sigma),\tau_D\bigr)+\kappa\,\tau_0 ,$$
--   where $\mathcal B_\theta$ is the beam-splitter output at transmissivity $\theta$. For a state $\mu$ with finite sixth moment, its *canonical weighted columns* are $x^\mu_m=\hat N^{3}\sqrt\mu\,|m\rangle$ $(m\in\mathbb{N}^n)$, so that $y_m=\hat N^{-3}x^\mu_m=\sqrt\mu|m\rangle$.
--
--   For $s\in\mathbb{R}$ and a bounded operator $Z$, the *generator pairing* is
--   $$\Gamma_s(x;Z)=\sum_{j=1}^n\sum_l\Bigl[(s+1)\Bigl(\langle\hat N^2a_jy_l,Z\hat N^2a_jy_l\rangle-\tfrac12\langle\hat N^2y_l,Z\hat N^2\hat n_jy_l\rangle-\tfrac12\langle\hat N^2\hat n_jy_l,Z\hat N^2y_l\rangle\Bigr)+s\Bigl(\langle\hat N^2a_j^\dagger y_l,Z\hat N^2a_j^\dagger y_l\rangle-\tfrac12\langle\hat N^2y_l,Z\hat N^2(\hat n_j+1)y_l\rangle-\tfrac12\langle\hat N^2(\hat n_j+1)y_l,Z\hat N^2y_l\rangle\Bigr)\Bigr]$$
--   with $\hat n_j=a_j^\dagger a_j$ (all vectors lie in $F$ because $\hat N^{2}a_j\hat N^{-3}$ etc. are bounded). Formally $\Gamma_s(x;Z)=\operatorname{Tr}\mu\,\mathcal L_s^*(\hat N^2Z\hat N^2)$, where $\mathcal L_s^*(K)=\sum_j(s+1)(a_j^\dagger Ka_j-\frac12\{\hat n_j,K\})+s(a_jKa_j^\dagger-\frac12\{a_ja_j^\dagger,K\})$ is the Heisenberg generator of the thermal-noise semigroup with mean photon number $s$.
--
--   For $\theta\in[0,1]$, a state $\nu$ with finite fourth moment and a bounded $T$, let $\mathcal C^{\theta}_{\nu}(T)$ and $\mathcal C'^{\theta}_{\nu}(T)$ be the weighted conditional operators: with $U_\theta$ the passive beam-splitter unitary of transmissivity $\theta$ on $\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$, they are defined by
--   $$\mathcal C^\theta_\nu(T)=\hat N^{-2}\,\Psi^{*}_{\theta,\nu}\bigl(\hat N^{2}T\hat N^{2}\bigr)\,\hat N^{-2},\qquad \langle x,\Psi^*_{\theta,\nu}(K)x'\rangle=\sum_m\bigl\langle U_\theta(x\otimes\sqrt\nu|m\rangle),(K\otimes\mathrm{Id})\,U_\theta(x'\otimes\sqrt\nu|m\rangle)\bigr\rangle ,$$
--   and likewise $\mathcal C'^\theta_\nu$ with $\sqrt\nu|m\rangle\otimes x$ (the known state in the first port). (In the file these are written with bounded weight ratios, as $\sum_mW_m^*(T\otimes\mathrm{Id})W_m$ for bounded $W_m$, so they are bounded operators; the displayed formula is their meaning.)
--
--   **Theorem.** Let $\rho,\sigma,\tau_D,\tau_0$ have finite sixth moments, let $a,b\in\mathbb{R}$, $d>0$, $r_0>0$ with
--   $$r_0=(1-\delta)\bigl(\eta a+(1-\eta)b\bigr)+\delta\,d ,$$
--   and assume $\tau_D$ and $\tau_0$ are the number-diagonal thermal states with mean photon numbers $d$ and $r_0$ per mode (matrix entries $\langle k|\tau_D|l\rangle=\delta_{kl}\prod_j\frac{1}{d+1}\bigl(\frac d{d+1}\bigr)^{k_j}$, and similarly for $\tau_0$ with $r_0$). Then $\omega=\omega(\rho,\sigma)$ has finite sixth moment, and for every bounded operator $B$
--   $$\Gamma_{r_0}(x^{\omega};B)=(1-\kappa)\Bigl[\Gamma_a\bigl(x^{\rho};\,\mathcal C^\eta_\sigma\,\mathcal C^{1-\delta}_{\tau_D}B\bigr)+\Gamma_b\bigl(x^{\sigma};\,\mathcal C'^\eta_\rho\,\mathcal C^{1-\delta}_{\tau_D}B\bigr)\Bigr].$$
--
--   Formally: the thermal-noise generator with mean $r_0$, evaluated on the output, equals $(1-\kappa)$ times the sum of the generators with means $a$ and $b$ acting on the two inputs, transported through the Heisenberg duals of the two beam splitters. The compatibility condition on $r_0$ says that $r_0$ is the output mean photon number when the inputs are thermal with means $a,b$; the $\kappa\tau_0$ component, being thermal with mean $r_0$, does not contribute.
--
--   **Formalization Note** The parameters are fields of the structure `Regularization n` (`R.output` is $\omega$); the canonical columns are `WeightedColumns.canonical` (built from `weightedRoot 3`), $\Gamma_s$ is `WeightedGenerator.pairing`, and `X.slice`, `X.sliceRight` are $\mathcal C$, $\mathcal C'$ with the columns $\hat N^{2}\sqrt\nu|m\rangle$. The existence of the moment proof `hm0` is part of the conclusion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/PhysicalMinimum.lean#L710-L751

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
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} (R : Regularization n)

theorem OAI.EntropyPhotonNumber.Regularization.canonical_output_generator (ρ σ : State n)
    (hmρ : FiniteMoment 6 ρ) (hmσ : FiniteMoment 6 σ)
    (hmD : FiniteMoment 6 R.τD) (hmO : FiniteMoment 6 R.τ0)
    (a b d r0 : ℝ) (hd : 0<d) (hr0 : 0<r0)
    (heq : r0=(1-R.δ)*(R.η*a+(1-R.η)*b)+(1-(1-R.δ))*d)
    (hD : ∀ k l, entry R.τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry R.τ0.op k l=if k=l then (thermalWeight n r0 k:ℂ) else 0)
    (B : Fock n →L[ℂ] Fock n) :
    ∃ hm0 : FiniteMoment 6 (R.output ρ σ),
      WeightedGenerator.pairing r0 (WeightedColumns.canonical (R.output ρ σ) hm0).vector B=
      ((1-R.κ:ℝ):ℂ)*
        (WeightedGenerator.pairing a (WeightedColumns.canonical ρ hmρ).vector
          ((WeightedColumns.canonical σ hmσ).slice R.η R.hη
            ((WeightedColumns.canonical R.τD hmD).slice (1-R.δ)
              ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ B))+
         WeightedGenerator.pairing b (WeightedColumns.canonical σ hmσ).vector
          ((WeightedColumns.canonical ρ hmρ).sliceRight R.η R.hη
            ((WeightedColumns.canonical R.τD hmD).slice (1-R.δ)
              ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ B))) := by sorry
