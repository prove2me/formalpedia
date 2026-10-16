-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_gibbs_slice_real_trace
-- name    : OAI.EntropyPhotonNumber.gibbs_slice_real_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:09:34.358994+00:00
-- url     : https://prove2.me/theorems/c0b38332-1c90-438b-9e15-c47d932a8e7f
-- title:
--   Real-valued trace formula for a state against a sliced Gibbs Hamiltonian on Fock space
-- statement:
--   Throughout, $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ is the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, and $|k|=k_1+\dots+k_n$ is the total photon number of $k$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ with $\sum_k\langle k|\rho|k\rangle=1$.
--
--   **Notation.** $M_4(\rho)=\sum_k(1+|k|)^4\langle k|\rho|k\rangle$ is the fourth number moment ($\rho$ has finite fourth moment if this series converges), and $E(\rho)=\sum_k|k|\,\langle k|\rho|k\rangle$ is the energy. $W_m$ is the diagonal operator $W_m|k\rangle=(1+|k|)^{-m/2}|k\rangle$. For $k>0$ and $B\ge0$ put $G_{k,B}=W_4(k\,I+W_3BW_3)^{-1}W_4$. For a Hilbert basis $(a_K)_{K\in\mathcal K}$ and weights $w_K\ge0$, and bounded operators $(V_i)_{i\in I}$, define in $[0,\infty]$
--   $$
--   \Sigma(x)=\sum_{i\in I}\sum_{K\in\mathcal K}w_K|\langle a_K,V_ix\rangle|^2,\qquad N(x)=\sum_k|k|\,|x_k|^2 .
--   $$
--
--   **Hypotheses.** Let $\rho$ be a state with finite fourth moment and eigenbasis $(b_j)_{j\in J}$: $\rho b_j=p_jb_j$, $p_j\ge0$, $\sum_jp_j=1$; put $v_j=\sqrt{p_j}\,b_j$. Let $\sum_i\|V_ix\|^2=\|x\|^2$ for all $x$, and let $\sigma$ be a state with $\sigma=\sum_{(i,j)}|V_iv_j\rangle\langle V_iv_j|$ and $\sum_Kw_K\operatorname{Re}\langle a_K,\sigma a_K\rangle$ convergent. Let $B\ge0$, $\alpha\ge0$, $\beta\ge0$ with
--   $$
--   \operatorname{Re}\langle x,Bx\rangle=\alpha\,\Sigma(W_1x)+\beta\,N(W_1x)\qquad\text{for all }x
--   $$
--   (an identity in $[0,\infty]$). Let $k>0$ and let $(c_l)_{l\in L}$ be a Hilbert basis with $G_{k,B}c_l=u_l^{-1}c_l$, $u_l>0$.
--
--   **Conclusion.**
--   $$
--   \sum_{l\in L}u_l\operatorname{Re}\langle c_l,\rho c_l\rangle=k\,M_4(\rho)+\alpha\sum_{K}w_K\operatorname{Re}\langle a_K,\sigma a_K\rangle+\beta\,E(\rho),
--   $$
--   where the left side converges (unconditionally) to the right side.
--
--   Formally the $u_l$ are the eigenvalues of the unbounded Gibbs Hamiltonian $G_{k,B}^{-1}$, so this computes the energy of $\rho$ for that Hamiltonian as a real number. Combined with the Gibbs variational principle, it shows that a minimizer of the corresponding free-energy functional is the Gibbs state.
--
--   **Formalization Note** The form identity is stated in `ENNReal` with weights `ENNReal.ofReal (w K)` and coefficients `ENNReal.ofReal α`, `ENNReal.ofReal β`; nonnegativity makes these equal to $w_K,\alpha,\beta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L443-L475

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
open QuantumTrace TraceEnsemble

theorem OAI.EntropyPhotonNumber.gibbs_slice_real_trace {n : ℕ} {J L K I : Type*}
    (c : HilbertBasis L ℂ (Fock n)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (ρ : State n) (heρ : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (hm : FiniteMoment 4 ρ)
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (σ : State n)
    (heσ : TraceEnsemble.operator (fun z : I × J => V z.1 (diagonalVector b p z.2)) = σ.op)
    (hc : Summable (fun j => w j*(inner ℂ (a j) (σ.op (a j))).re))
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a (fun j => ENNReal.ofReal (w j)) V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k)
    (heK : ∀ l, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l) :
    HasSum (fun l => u l*(inner ℂ (c l) (ρ.op (c l))).re)
      (k*numberMoment 4 ρ + α*(∑' j, w j*(inner ℂ (a j) (σ.op (a j))).re) + β*energy ρ) := by sorry
