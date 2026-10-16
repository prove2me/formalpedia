-- Prove2me | Theorems.Thm_OAI_QuantumTrace_quantum_klein
-- name    : OAI.QuantumTrace.quantum_klein
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:06:23.856565+00:00
-- url     : https://prove2.me/theorems/52726e68-3fe1-4a94-a622-01961eac13b5
-- title:
--   Klein's inequality for operators with orthonormal eigenbases, with its equality case
-- statement:
--   Let $E$ be a complex inner product space with Hilbert bases $(b_i)_{i\in I}$ and $(c_j)_{j\in J}$. Let $T$ and $S$ be bounded operators on $E$ with $S$ symmetric ($\langle Sx,y\rangle=\langle x,Sy\rangle$), and assume
--   $$
--   Tb_i=p_ib_i,\quad p_i\ge0,\ \sum_ip_i=1;\qquad Sc_j=q_jc_j,\quad q_j>0,\ \sum_jq_j=1 .
--   $$
--   Let $\eta(t)=-t\log t$ (with $\eta(0)=0$). Suppose the series
--   $$
--   H=\sum_{i\in I}\eta(p_i),\qquad C=\sum_{j\in J}\operatorname{Re}\langle c_j,Tc_j\rangle\,(-\log q_j)
--   $$
--   both converge (unconditionally) in $\mathbb{R}$. Then
--
--   1. $H\le C$;
--   2. if $H=C$, then $T=S$.
--
--   In density-operator language, $H$ is the von Neumann entropy $-\operatorname{Tr}T\log T$ and $C$ is the cross entropy $-\operatorname{Tr}T\log S$, so the theorem is Klein's inequality $-\operatorname{Tr}T\log T\le-\operatorname{Tr}T\log S$, with equality only when $T=S$. It is the basic tool behind the Gibbs variational principle and the entropy-versus-cross-entropy bounds used later.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L155-L189

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
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem OAI.QuantumTrace.quantum_klein (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    {T S : E →L[ℂ] E} (hs : S.IsSymmetric)
    {p : I → ℝ} {q : J → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
    (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
    (heT : ∀ i, T (b i) = (p i : ℂ) • b i)
    (heS : ∀ j, S (c j) = (q j : ℂ) • c j)
    {H C : ℝ} (hh : HasSum (fun i => Real.negMulLog (p i)) H)
    (hc : HasSum (fun j => (inner ℂ (c j) (T (c j))).re * (-Real.log (q j))) C) :
    H ≤ C ∧ (H = C → T = S) := by sorry
