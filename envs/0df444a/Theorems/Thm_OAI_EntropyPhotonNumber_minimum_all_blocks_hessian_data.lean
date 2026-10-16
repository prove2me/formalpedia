-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_minimum_all_blocks_hessian_data
-- name    : OAI.EntropyPhotonNumber.minimum_all_blocks_hessian_data
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:40:54.365979+00:00
-- url     : https://prove2.me/theorems/bf191e3a-c9d2-4e42-b7e9-fa0b18e01c27
-- title:
--   Gibbs structure and block Hessian bounds at a minimizer of a regularized entropy functional
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, total number $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, and the diagonal weight $\hat N=1+\sum_ja_j^\dagger a_j$, i.e. $\hat N|k\rangle=(1+|k|)|k\rangle$. A state is a positive bounded operator on $F$ whose number-basis diagonal sums to $1$. For a state $\rho$ write $S(\rho)=-\operatorname{Tr}\rho\log\rho$, $E(\rho)=\sum_k|k|\,\rho_{kk}$ and $M_4(\rho)=\sum_k(1+|k|)^4\rho_{kk}$; $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$.
--
--   A *Kraus flow* consists of bounded operators $(V_i)_{i}$ on $F$ with $\sum_i\|V_ix\|^2=\|x\|^2$ for all $x$, a constant $F_0\ge0$ with $\sum_i\langle V_ix,\hat n V_ix\rangle\le\langle x,\hat nx\rangle+F_0\|x\|^2$ (where $\hat n=\sum_ja_j^\dagger a_j$, both sides in $[0,\infty]$), and a map $\mathcal F$ on states such that $\mathcal F(\rho)=\sum_{i,l}|V_iv_l\rangle\langle V_iv_l|$ whenever $\rho=\sum_l|v_l\rangle\langle v_l|$ with $\sum_l\|v_l\|^2=1$, and $\mathcal F$ preserves finite energy. Its Heisenberg dual is $\mathcal F^*(Z)=\sum_iV_i^*ZV_i$.
--
--   A *Gibbs representation of $\rho$ with quartic coefficient $k$* consists of a positive bounded operator $B_\rho$, a Hilbert basis $(g_j)_{j}$ of $F$ and numbers $u_j>0$ with $\mathcal Z=\sum_je^{-u_j}<\infty$ such that $\hat N^{-2}\bigl(k+\hat N^{-3/2}B_\rho\hat N^{-3/2}\bigr)^{-1}\hat N^{-2}g_j=u_j^{-1}g_j$ for all $j$ and $\rho=\sum_j\frac{e^{-u_j}}{\mathcal Z}|g_j\rangle\langle g_j|$ (moreover $\rho$ is injective and has finite seventh moment). Formally $\rho=e^{-H}/\mathcal Z$ with $H=k\hat N^4+\hat N^{1/2}B_\rho\hat N^{1/2}$. Its *quartic logarithm* is the bounded operator
--   $$\mathcal L_\rho=k\,\mathrm{Id}+\hat N^{-3/2}B_\rho\hat N^{-3/2}+(\log\mathcal Z)\,\hat N^{-4},$$
--   formally $\hat N^{-2}(-\log\rho)\hat N^{-2}$.
--
--   For a Hilbert basis $(e_j)$ and weights $w_j>0$ with $\sum_j w_j=1$, write the BKM variance of a bounded operator $T$ as
--   $$\mathrm{Var}_{e,w}(T)=\sum_{i,j}L(w_i,w_j)\,|\langle e_i,Te_j\rangle|^2-\Bigl|\sum_jw_j\langle e_j,Te_j\rangle\Bigr|^2 ,$$
--   with $L$ the logarithmic mean.
--
--   **Theorem.** Let $\mathcal F$ be a Kraus flow, $r>0$, and $\tau=\tau_r$ the thermal state with mean photon number $r$ in each mode. Let $\kappa\in(0,1]$, $c>0$, $a>0$, $\beta\ge0$, $\zeta>0$. Let $\rho$ be a state with finite fourth moment, and let $(d_j)_{j\in J}$ be a Hilbert basis and $q_j>0$, $\sum_jq_j=1$, such that
--   $$\rho_0:=(1-\kappa)\mathcal F(\rho)+\kappa\tau\quad\text{satisfies}\quad\rho_0d_j=q_jd_j\ \text{ for all }j .$$
--   Suppose $\rho$ minimizes
--   $$\Phi(\sigma)=c\,S\bigl((1-\kappa)\mathcal F(\sigma)+\kappa\tau\bigr)-a\,S(\sigma)+\beta E(\sigma)+\zeta M_4(\sigma)$$
--   among all states $\sigma$ with finite fourth moment. Then there is a Gibbs representation $(B_\rho,g,u)$ of $\rho$ with quartic coefficient $\zeta/a$ such that:
--
--   1. for every $x\in F$, in $[0,\infty]$,
--   $$\langle x,B_\rho x\rangle=\frac{c(1-\kappa)}{a}\sum_i\sum_j(-\log q_j)\,\bigl|\langle d_j,V_i\hat N^{-1/2}x\rangle\bigr|^2+\frac\beta a\sum_k|k|\,\bigl|(\hat N^{-1/2}x)_k\bigr|^2 ;$$
--   2. for every finite set $s\subseteq J$ and every complex matrix $Z=(Z_{ii'})_{i,i'\in s}$, with $\mathsf B_s(Z)=\sum_{i,i'\in s}Z_{ii'}|d_i\rangle\langle d_{i'}|$,
--   $$(1-\kappa)^2\,\mathrm{Var}_{g,\,e^{-u}/\mathcal Z}\bigl(\mathcal F^*(\mathsf B_s(Z))\bigr)\le\frac ac\,\mathrm{Var}_{d,q}\bigl(\mathsf B_s(Z)\bigr).$$
--
--   Item 1 identifies the minimizer as a Gibbs state for the Hamiltonian $\frac\zeta a\hat N^4+\frac{c(1-\kappa)}{a}\mathcal F^*(-\log\rho_0)+\frac\beta a\hat n$ (formally), and item 2 is the second-order (Hessian) optimality condition: the flow contracts the logarithmic-mean metric from $\rho_0$ back to $\rho$ on every finite block of the eigenbasis of $\rho_0$.
--
--   **Formalization Note** The Gibbs representation is the structure `GibbsData n (ζ/a) ρ`; item 1 is an identity in `ℝ≥0∞` written with `sliceMoment`, `numberVectorMoment` and `energyInverse n` $=\hat N^{-1/2}$. The block $\mathsf B_s(Z)$ is `FiniteBlock.block` for the basis $d$ reindexed by $s\sqcup s^{\mathrm c}$, and $\mathrm{Var}$ is `BKM.variance`. The thermal state is fixed by the hypothesis `τ = thermalState n r hr`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L2679-L2746

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

open OAI OAI.EntropyPhotonNumber
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
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]

theorem OAI.EntropyPhotonNumber.minimum_all_blocks_hessian_data
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ,
      (∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re =
        ENNReal.ofReal (c*(1-κ)/a)*
          sliceMoment d (fun j => ENNReal.ofReal (-Real.log (q j))) F.V (energyInverse n x)+
        ENNReal.ofReal (β/a)*numberVectorMoment (energyInverse n x)) ∧
      ∀ (s : Finset J) (Z : Matrix s s ℂ),
      (1-κ)^2*BKM.variance G.basis (gibbsWeight G.eigenval)
        (F.dual (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z) := by sorry
