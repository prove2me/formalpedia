-- Prove2me | Theorems.Thm_OAI_QuantumTrace_spectral_gibbs_attains
-- name    : OAI.QuantumTrace.spectral_gibbs_attains
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:07:41.005981+00:00
-- url     : https://prove2.me/theorems/25d8f40f-eee4-4088-89f2-5a4fbd3791e7
-- title:
--   The spectral Gibbs state attains the free energy $-\log Z$
-- statement:
--   Let $E$ be a complex Hilbert space, let $(b_j)_{j\in J}$ be a Hilbert basis indexed by a nonempty set $J$, and let $(a_i)_{i\in I}$ be any Hilbert basis of $E$. Let $u:J\to\mathbb{R}$ satisfy $u_j\ge0$, and assume that both $\sum_je^{-u_j}$ and $\sum_je^{-u_j/2}$ converge. Put
--   $$
--   Z=\sum_{j}e^{-u_j},\qquad g_j=\frac{e^{-u_j}}{Z},\qquad \omega=\sum_jg_j\,|b_j\rangle\langle b_j| ,
--   $$
--   so $\omega$ is the bounded operator that is diagonal in the basis $(b_j)$ with eigenvalues $g_j$. Let $\eta(\omega)$ be obtained from $\omega$ by continuous functional calculus with $\eta(t)=-t\log t$. Then:
--
--   1. the series $\sum_ju_j\operatorname{Re}\langle b_j,\omega b_j\rangle$ converges;
--   2. the series $\sum_i\operatorname{Re}\langle a_i,\eta(\omega)a_i\rangle$ converges;
--   3. the two sums satisfy
--   $$
--   \sum_{j}u_j\operatorname{Re}\langle b_j,\omega b_j\rangle-\sum_{i}\operatorname{Re}\langle a_i,\eta(\omega)a_i\rangle=-\log Z .
--   $$
--
--   If $u_j$ are the energies of a Hamiltonian with eigenbasis $(b_j)$, then $\omega$ is its Gibbs state, the first sum is its mean energy and the second is its von Neumann entropy computed in an arbitrary basis. The theorem says that the Gibbs state attains the value $-\log Z$ of the free energy. Together with the Gibbs variational inequality, which gives the lower bound $-\log Z$ for every state, this identifies the Gibbs state as the minimizer.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L239-L290

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

open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
variable {J : Type*}

theorem OAI.QuantumTrace.spectral_gibbs_attains {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nonempty J] {I : Type*} (a : HilbertBasis I ℂ E)
    (b : HilbertBasis J ℂ E) (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hheat : Summable (fun j => Real.exp (-u j)))
    (hhalf : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    let ω := spectralGibbs b u hheat
    Summable (fun j => u j*(inner ℂ (b j) (ω (b j))).re) ∧
      Summable (fun i => (inner ℂ (a i) (entropyOperator ω (a i))).re) ∧
      (∑' j, u j*(inner ℂ (b j) (ω (b j))).re) -
        (∑' i, (inner ℂ (a i) (entropyOperator ω (a i))).re) = -Real.log (heatPartition u) := by sorry
