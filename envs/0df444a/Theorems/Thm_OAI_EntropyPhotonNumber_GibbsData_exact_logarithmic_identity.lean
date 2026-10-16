-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_GibbsData_exact_logarithmic_identity
-- name    : OAI.EntropyPhotonNumber.GibbsData.exact_logarithmic_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:42:58.000233+00:00
-- url     : https://prove2.me/theorems/e8e46b03-8d9f-4721-b018-b8903eddcf12
-- title:
--   Exact operator identity for the quartic logarithm of a Gibbs minimizer
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, total number $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, and the diagonal weight $\hat N=1+\sum_ja_j^\dagger a_j$, i.e. $\hat N|k\rangle=(1+|k|)|k\rangle$. A state is a positive bounded operator on $F$ whose number-basis diagonal sums to $1$. For a state $\rho$ write $S(\rho)=-\operatorname{Tr}\rho\log\rho$, $E(\rho)=\sum_k|k|\,\rho_{kk}$ and $M_4(\rho)=\sum_k(1+|k|)^4\rho_{kk}$; $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$.
--
--   A *Kraus flow* consists of bounded operators $(V_i)_{i}$ on $F$ with $\sum_i\|V_ix\|^2=\|x\|^2$ for all $x$, a constant $F_0\ge0$ with $\sum_i\langle V_ix,\hat n V_ix\rangle\le\langle x,\hat nx\rangle+F_0\|x\|^2$ (where $\hat n=\sum_ja_j^\dagger a_j$, both sides in $[0,\infty]$), and a map $\mathcal F$ on states such that $\mathcal F(\rho)=\sum_{i,l}|V_iv_l\rangle\langle V_iv_l|$ whenever $\rho=\sum_l|v_l\rangle\langle v_l|$ with $\sum_l\|v_l\|^2=1$, and $\mathcal F$ preserves finite energy. Its Heisenberg dual is $\mathcal F^*(Z)=\sum_iV_i^*ZV_i$.
--
--   A *Gibbs representation of $\rho$ with quartic coefficient $k$* consists of a positive bounded operator $B_\rho$, a Hilbert basis $(g_j)_{j}$ of $F$ and numbers $u_j>0$ with $\mathcal Z=\sum_je^{-u_j}<\infty$ such that $\hat N^{-2}\bigl(k+\hat N^{-3/2}B_\rho\hat N^{-3/2}\bigr)^{-1}\hat N^{-2}g_j=u_j^{-1}g_j$ for all $j$ and $\rho=\sum_j\frac{e^{-u_j}}{\mathcal Z}|g_j\rangle\langle g_j|$ (moreover $\rho$ is injective and has finite seventh moment). Formally $\rho=e^{-H}/\mathcal Z$ with $H=k\hat N^4+\hat N^{1/2}B_\rho\hat N^{1/2}$. Its *quartic logarithm* is the bounded operator
--   $$\mathcal L_\rho=k\,\mathrm{Id}+\hat N^{-3/2}B_\rho\hat N^{-3/2}+(\log\mathcal Z)\,\hat N^{-4},$$
--   formally $\hat N^{-2}(-\log\rho)\hat N^{-2}$.
--
--   **Theorem.** Let $\rho$ have a Gibbs representation $(B_\rho,g,u)$ with quartic coefficient $k$, let $\mathcal F=(V_i)$ be a Kraus flow and $\tau$ a state. Let $r>0$ and $0<\delta\le1$ with $\delta\,\tau_r\le\tau$ in operator order, where $\tau_r$ is the thermal state with mean photon number $r$ per mode. Let $(b_j)_{j\in J}$ be a Hilbert basis and $p_j>0$, $\sum_jp_j=1$, with $\tau b_j=p_jb_j$. Let $\alpha,\beta\ge0$ and suppose that for all $x\in F$, in $[0,\infty]$,
--   $$\langle x,B_\rho x\rangle=\alpha\sum_i\sum_j(-\log p_j)\,\bigl|\langle b_j,V_i\hat N^{-1/2}x\rangle\bigr|^2+\beta\sum_k|k|\,\bigl|(\hat N^{-1/2}x)_k\bigr|^2 .$$
--   Then there exist positive bounded operators $C,D$ on $F$ such that for all $x$
--   $$\langle x,Cx\rangle=\sum_i\sum_j(-\log p_j)\,\bigl|\langle b_j,V_i\hat N^{-2}x\rangle\bigr|^2,\qquad\langle x,Dx\rangle=\sum_k|k|\,\bigl|(\hat N^{-2}x)_k\bigr|^2$$
--   (in $[0,\infty]$), and
--   $$\mathcal L_\rho=k\,\mathrm{Id}+\alpha\,C+\beta\,D+(\log\mathcal Z)\,\hat N^{-4}.$$
--
--   Formally $C=\hat N^{-2}\mathcal F^*(-\log\tau)\hat N^{-2}$ and $D=\hat N^{-2}\hat n\hat N^{-2}$, so the identity is the bounded, sandwiched version of the Euler–Lagrange equation $-\log\rho=k\hat N^4+\alpha\,\mathcal F^*(-\log\tau)+\beta\hat n+\log\mathcal Z$. Having it as an exact identity of bounded operators lets one pair $-\log\rho$ with unbounded generators rigorously.
--
--   **Formalization Note** The Gibbs representation is `GibbsData n k ρ` and $\mathcal L_\rho$ is `G.quarticLogarithm`; quadratic forms are compared in `ℝ≥0∞` via `ENNReal.ofReal`; $\hat N^{-1/2}$ and $\hat N^{-2}$ are `inversePower rootNumberWeight _ 1` and `_ 4` (with `rootNumberWeight` $=\sqrt{1+|k|}$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L2819-L2875

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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.GibbsData
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
open QuantumTrace
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem OAI.EntropyPhotonNumber.GibbsData.exact_logarithmic_identity {J : Type*}
    (F : KrausFlow n) (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) F.V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ C D : Fock n →L[ℂ] Fock n, C.IsPositive ∧ D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (C x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) F.V
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      G.quarticLogarithm = (k:ℂ) • (1 : Fock n →L[ℂ] Fock n)+(α:ℂ) • C+(β:ℂ) • D+
        (Real.log (heatPartition G.eigenval):ℂ) •
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
            inversePower rootNumberWeight rootNumberWeight_one_le 4) := by sorry
