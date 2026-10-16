-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_gibbs_slice_trace
-- name    : OAI.EntropyPhotonNumber.gibbs_slice_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:04:49.319248+00:00
-- url     : https://prove2.me/theorems/1031445e-2350-4ccc-9aed-206b5ac7ae23
-- title:
--   Trace of a state against a sliced Gibbs Hamiltonian on Fock space, as an identity in $[0,\infty]$
-- statement:
--   Throughout, $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ is the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, and $|k|=k_1+\dots+k_n$ is the total photon number of $k$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ with $\sum_k\langle k|\rho|k\rangle=1$.
--
--   **Notation.**
--   - $M_4(\rho)=\sum_k(1+|k|)^4\langle k|\rho|k\rangle$ is the fourth number moment; $\rho$ has *finite fourth moment* if this series converges. $E(\rho)=\sum_k|k|\,\langle k|\rho|k\rangle$ is the energy.
--   - $W_m$ is the diagonal operator $W_m|k\rangle=(1+|k|)^{-m/2}|k\rangle$.
--   - For $k>0$ and a positive bounded operator $B$, put $G_{k,B}=W_4\,(k\,I+W_3BW_3)^{-1}\,W_4$ (a bounded operator).
--   - For a Hilbert basis $a=(a_K)_{K\in\mathcal K}$ of $\mathcal F_n$ and weights $w:\mathcal K\to[0,\infty]$: $\beta_{a,w}(x)=\sum_K w_K\,|\langle a_K,x\rangle|^2$ and $\mathbb E_{a,w}(\sigma)=\sum_Kw_K\operatorname{Re}\langle a_K,\sigma a_K\rangle$, both in $[0,\infty]$.
--   - For bounded operators $(V_i)_{i\in I}$: $\Sigma(x)=\sum_i\beta_{a,w}(V_ix)\in[0,\infty]$, and $N(x)=\sum_k|k|\,|x_k|^2\in[0,\infty]$.
--   - $[t]_+=\max(t,0)$.
--
--   **Hypotheses.** Let $\rho$ be a state with finite fourth moment, diagonalized by a Hilbert basis $(b_j)_{j\in J}$: $\rho b_j=p_jb_j$, $p_j\ge0$, $\sum_jp_j=1$; put $v_j=\sqrt{p_j}\,b_j$. Let $(V_i)_{i\in I}$ satisfy $\sum_i\|V_ix\|^2=\|x\|^2$ for all $x$, and let $\sigma$ be a state with $\sigma=\sum_{(i,j)\in I\times J}|V_iv_j\rangle\langle V_iv_j|$. Let $B\ge0$ and $\alpha,\beta\in\mathbb{R}$ with
--   $$
--   \operatorname{Re}\langle x,Bx\rangle=[\alpha]_+\,\Sigma(W_1x)+[\beta]_+\,N(W_1x)\qquad\text{in }[0,\infty]\text{ for all }x\in\mathcal F_n .
--   $$
--   Let $k>0$ and let $(c_l)_{l\in L}$ be a Hilbert basis with $G_{k,B}\,c_l=u_l^{-1}c_l$, $u_l>0$.
--
--   **Conclusion.** There is a real number $\mathcal E$ such that $\sum_l u_l\operatorname{Re}\langle c_l,\rho c_l\rangle$ converges (unconditionally) to $\mathcal E$ and, in $[0,\infty]$,
--   $$
--   [\mathcal E]_+=k\,M_4(\rho)+[\alpha]_+\,\mathbb E_{a,w}(\sigma)+[\beta]_+\,E(\rho).
--   $$
--
--   Formally, $u_l$ are the eigenvalues of the unbounded Gibbs Hamiltonian $G_{k,B}^{-1}=W_4^{-1}(k+W_3BW_3)W_4^{-1}$, so the left side is the trace of $\rho$ against this Hamiltonian; the theorem evaluates it as a fourth-moment penalty plus a "sliced" expectation in the output state $\sigma$ plus an energy term. It is the extended-real precursor of the real-valued trace formula used to identify minimizers of the one-port entropy functional with Gibbs states.
--
--   **Formalization Note** $[t]_+$ is `ENNReal.ofReal t`; since $B\ge0$ the left side of the form identity is just $\operatorname{Re}\langle x,Bx\rangle$. $W_m$ is `inversePower rootNumberWeight _ m` with weights $\sqrt{1+|k|}$, and $W_1$ is `energyInverse n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L2111-L2172

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

theorem OAI.EntropyPhotonNumber.gibbs_slice_trace {n : ℕ} {J L K I : Type*}
    (c : HilbertBasis L ℂ (Fock n)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (ρ : State n) (heρ : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (hm : FiniteMoment 4 ρ)
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ≥0∞)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (σ : State n)
    (heσ : TraceEnsemble.operator (fun z : I × J => V z.1 (diagonalVector b p z.2)) = σ.op)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ}
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a w V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k)
    (heK : ∀ l, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l) :
    ∃ E : ℝ, HasSum (fun l => u l*(inner ℂ (c l) (ρ.op (c l))).re) E ∧
      ENNReal.ofReal E = ENNReal.ofReal k*ENNReal.ofReal (numberMoment 4 ρ)+
        (ENNReal.ofReal α*basisExpectation a w σ.op+
         ENNReal.ofReal β*ENNReal.ofReal (energy ρ)) := by sorry
