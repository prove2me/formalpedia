-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_GibbsData_crossEntropy_hamiltonian
-- name    : OAI.EntropyPhotonNumber.GibbsData.crossEntropy_hamiltonian
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:12:43.06801+00:00
-- url     : https://prove2.me/theorems/4fcbe2a1-28fa-469a-8062-4dd0d243ed82
-- title:
--   Cross entropy against a Gibbs state equals the linearized free energy plus $\log Z$
-- statement:
--   Throughout, $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ is the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, and $|k|=k_1+\dots+k_n$ is the total photon number of $k$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ with $\sum_k\langle k|\rho|k\rangle=1$.
--
--   **Notation.**
--   - $M_4(\sigma)=\sum_k(1+|k|)^4\langle k|\sigma|k\rangle$ and $E(\sigma)=\sum_k|k|\langle k|\sigma|k\rangle$; finite fourth moment means the first series converges.
--   - $W_m|k\rangle=(1+|k|)^{-m/2}|k\rangle$, and $N(x)=\sum_k|k|\,|x_k|^2\in[0,\infty]$.
--   - For a Hilbert basis $(a_j)_{j\in J}$ and $p_j>0$, the cross entropy of a state $\pi$ is $C_{a,p}(\pi)=\sum_j(-\log p_j)\operatorname{Re}\langle a_j,\pi a_j\rangle$.
--
--   **Gibbs data.** Let $k>0$ and let $\rho$ be a state carrying Gibbs data with parameter $k$:
--   - a positive bounded operator $B$, a nonempty index set $L$, a Hilbert basis $(d_l)_{l\in L}$ and numbers $u_l>0$ with $Z=\sum_le^{-u_l}<\infty$;
--   - $W_4(k\,I+W_3BW_3)^{-1}W_4\,d_l=u_l^{-1}d_l$ for every $l$;
--   - $\rho=\sum_lg_l|d_l\rangle\langle d_l|$ with $g_l=e^{-u_l}/Z$, $\rho$ injective, and $\rho$ of finite seventh moment.
--
--   **Hypotheses.** Let $(a_j)_{j\in J}$ be a Hilbert basis and let $p_j>0$ with $\sum_jp_j=1$. Let $\mathcal F$ be a Kraus flow with Kraus operators $(V_i)_{i\in I}$ and state map $\Phi$:
--   - $\sum_i\|V_ix\|^2=\|x\|^2$, and $\sum_iN(V_ix)\le N(x)+F_0\|x\|^2$ for a constant $F_0\ge0$;
--   - $\Phi(\pi)=\sum_{i,j}|V_iv_j\rangle\langle V_iv_j|$ whenever $\pi=\sum_j|v_j\rangle\langle v_j|$ with $\sum_j\|v_j\|^2=1$, and $\Phi$ preserves finite energy.
--
--   Let $\alpha,\beta\ge0$ and suppose that for all $x$, in $[0,\infty]$,
--   $$
--   \operatorname{Re}\langle x,Bx\rangle=\alpha\sum_{i}\sum_{j}(-\log p_j)\,|\langle a_j,V_iW_1x\rangle|^2+\beta\,N(W_1x).
--   $$
--   Let $\sigma$ be a state with finite fourth moment such that the series defining $C_{a,p}(\Phi(\sigma))$ converges.
--
--   **Conclusion.** The series on the left converges (unconditionally), and
--   $$
--   \sum_{l\in L}(-\log g_l)\,\operatorname{Re}\langle d_l,\sigma d_l\rangle=k\,M_4(\sigma)+\alpha\,C_{a,p}(\Phi(\sigma))+\beta\,E(\sigma)+\log Z .
--   $$
--
--   The left side is the cross entropy $-\operatorname{Tr}\sigma\log\rho$ of $\sigma$ against the Gibbs state $\rho$. The identity expresses it through the linear terms of the free-energy functional. This is the form in which the Gibbs structure of a minimizer is fed into the entropy estimates.
--
--   **Formalization Note** The Gibbs data are the structure `GibbsData n k ρ`, and $C_{a,p}$ is `crossEntropy a p`, a `tsum`. The form identity uses `ENNReal.ofReal` for $-\log p_j$, $\alpha$ and $\beta$, all of which are nonnegative here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L793-L819

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
open QuantumTrace TraceEnsemble
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem OAI.EntropyPhotonNumber.GibbsData.crossEntropy_hamiltonian {J : Type*}
    (a : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (F : KrausFlow n) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hk : 0 < k)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re =
      ENNReal.ofReal α*sliceMoment a (fun j => ENNReal.ofReal (-Real.log (p j))) F.V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    (σ : State n) (hm : FiniteMoment 4 σ)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (a j) ((F.map σ).op (a j))).re)) :
    HasSum (fun j => (-Real.log (gibbsWeight G.eigenval j))*(inner ℂ (G.basis j) (σ.op (G.basis j))).re)
      (k*numberMoment 4 σ+α*crossEntropy a p (F.map σ)+β*energy σ+Real.log (heatPartition G.eigenval)) := by sorry
