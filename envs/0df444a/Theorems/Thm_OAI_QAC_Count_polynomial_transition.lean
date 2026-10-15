-- Prove2me | Theorems.Thm_OAI_QAC_Count_polynomial_transition
-- name    : OAI.QAC.Count.polynomial_transition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:43:20.657079+00:00
-- url     : https://prove2.me/theorems/ab6332d7-9dde-4389-9477-45a7d443047c
-- title:
--   Transition bounds for small product projections extend to polynomials in the mismatch count
-- statement:
--   Let $D,M$ be counts on $N$ qubits and let $U$ be an arbitrary $N$-qubit operator; write $\operatorname{conj}_U(X)=UXU^{*}$, $P_K^0$ for the zero-mismatch projection of a count $K$, $\operatorname{supp}K$ for its support, and $[\mathcal N_M\ge r]$ for the high projection of the mismatch count of $M$. For a real polynomial $p$ let
--   $$p(\mathcal N_D)=\sum_{F\subseteq\operatorname{supp}D}p(|F|)\,P_D^F$$
--   be $p$ evaluated at the mismatch operator of $D$ through its spectral decomposition; here $P_D^F$ is the projection onto the states whose set of mismatched qubits, relative to the axes of $D$, is exactly $F$. Let $\|p\|_N=\sum_k|c_k|N^k$ be the weight of $p=\sum_kc_kX^k$.
--
--   Let $r,\mu,\delta\in\mathbb R$ with $\delta\ge0$ and $\deg p\le\mu$, and assume that every count $A$ on $N$ qubits with $|\operatorname{supp}A|\le\mu$ satisfies $\bigl\|[\mathcal N_M\ge r]\operatorname{conj}_U(P_A^0)\,P_M^0\bigr\|\le\delta$. Then
--   $$
--   \bigl\|[\mathcal N_M\ge r]\,\operatorname{conj}_U\bigl(p(\mathcal N_D)\bigr)\,P_M^0\bigr\|\le\|p\|_N\,\delta .
--   $$
--
--   Thus a transition bound that is known only for product projections with support of size at most $\mu$ transfers to every polynomial of degree at most $\mu$ in a mismatch operator, at the price of the weight of the polynomial. Combined with a low-degree, low-weight polynomial approximating the indicator of $0$, it controls the evolved projection $\operatorname{conj}_U(P_D^0)$ in the backward step of the localization argument.
--
--   **Formalization Note** $p(\mathcal N_D)$ is `D.polynomial p`, the degree is `natDegree` (the zero polynomial has degree $0$), and the weight is `weight N p` with $N$ cast to a real number. Unitarity of $U$ is not assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Backward.lean#L45-L63

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem OAI.QAC.Count.polynomial_transition {N : ℕ} (D M : Count N) (U : Operator N)
    (p : Polynomial ℝ) (r μ δ : ℝ) (hδ : 0 ≤ δ) (hp : (p.natDegree:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ weight N p*δ := by sorry
