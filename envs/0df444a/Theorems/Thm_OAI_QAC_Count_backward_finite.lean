-- Prove2me | Theorems.Thm_OAI_QAC_Count_backward_finite
-- name    : OAI.QAC.Count.backward_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:45:10.741769+00:00
-- url     : https://prove2.me/theorems/c45d9377-c331-4f6f-b8c8-2c115a8e7d5f
-- title:
--   Backward step: bounding a projection transition by a polynomial approximant and a reverse transition
-- statement:
--   Let $M,D$ be counts on $N$ qubits, $U$ a unitary $N$-qubit operator and $p$ a real polynomial. Write $\operatorname{conj}_U(X)=UXU^{*}$, $P_K^0$ for the zero-mismatch projection of a count $K$, $[\mathcal N_K\ge x]$ and $[\mathcal N_K<x]=I-[\mathcal N_K\ge x]$ for the spectral projections of its mismatch count, and $p(\mathcal N_D)=\sum_{F\subseteq\operatorname{supp}D}p(|F|)\,P_D^F$ for $p$ evaluated at the mismatch operator of $D$, where $P_D^F$ projects onto the states whose set of mismatched qubits relative to the axes of $D$ is exactly $F$. Let $r,b,A,B,E,T\in\mathbb R$ and assume:
--
--   1. $\bigl\|[\mathcal N_M\ge r]\operatorname{conj}_U\bigl(p(\mathcal N_D)\bigr)\,P_M^0\bigr\|\le A$ (transition of the approximant);
--   2. $\|p(\mathcal N_D)\|\le B$;
--   3. $\bigl\|\bigl(P_D^0-p(\mathcal N_D)\bigr)\,[\mathcal N_D<b]\bigr\|\le E$ (approximation error on low mismatch counts);
--   4. $\bigl\|[\mathcal N_D\ge b]\,U^{*}P_M^0U\,P_D^0\bigr\|\le T$ (reverse transition).
--
--   Then
--   $$
--   \bigl\|[\mathcal N_M\ge r]\,\operatorname{conj}_U(P_D^0)\,P_M^0\bigr\|^2\le A+E+(1+B)\,T .
--   $$
--
--   This is the finite, non-asymptotic form of the backward step in the localization argument. The reverse transition 4 involves the inverse circuit $U^{*}$, the roles of $M$ and $D$ exchanged and a larger threshold $b$, and is supplied by the induction hypothesis at a larger scale; bound 1 comes from transition bounds for small product projections through a low-degree polynomial, and bound 3 from the polynomial being close to the indicator of $0$ on low mismatch counts. When all four quantities are exponentially small, taking a square root gives the transition bound at the smaller scale.
--
--   **Formalization Note** Unitarity is `hU : U ∈ unitary (Operator N)`, the norm is the Euclidean operator norm on complex matrices indexed by $\{0,1\}^N$, and $p(\mathcal N_D)$ is `D.polynomial p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Backward.lean#L65-L103

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

theorem OAI.QAC.Count.backward_finite {N : ℕ} (M D : Count N) (U : Operator N) (hU : U ∈ unitary (Operator N))
    (p : Polynomial ℝ) (r b A B E T : ℝ)
    (hx : ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ A)
    (hp : ‖D.polynomial p‖ ≤ B)
    (he : ‖(D.zero-D.polynomial p)*D.low b‖ ≤ E)
    (ht : ‖D.high b*star U*M.zero*U*D.zero‖ ≤ T) :
    ‖M.high r*conjugate U D.zero*M.zero‖^2 ≤ A+E+(1+B)*T := by sorry
