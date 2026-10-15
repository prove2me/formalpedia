-- Prove2me | Theorems.Thm_OAI_QAC_IsCircuit_star_mem
-- name    : OAI.QAC.IsCircuit.star_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:32:50.273442+00:00
-- url     : https://prove2.me/theorems/3a812e35-ecdd-46ab-9c55-75bc6eb11860
-- title:
--   The adjoint of a depth-$d$ normal-form circuit is a depth-$d$ normal-form circuit
-- statement:
--   Normal-form circuits on $N$ qubits are built from two kinds of layers. A local layer is a tensor product $\bigotimes_{i}L_i$ of one-qubit unitaries $L_i\in U(2)$. A reflection layer is a product $\prod_{j=1}^m\bigl(I-2\Pi^{A_j}_0\bigr)$ of reflections about the product projections $\Pi^{A_j}_0$ of counts $A_1,\dots,A_m$ with pairwise disjoint supports (a count $A$ has a support $S\subseteq[N]$ and unit vectors $v_i\in\mathbb{C}^2$ for $i\in S$, and $\Pi^A_0$ is the tensor product of $|v_i\rangle\langle v_i|$ over $i\in S$ and $I$ elsewhere). The class $\mathrm{Circ}_d$ of depth-$d$ circuits is defined recursively: $U\in\mathrm{Circ}_0$ iff $U$ is a local layer, and $U\in\mathrm{Circ}_{d+1}$ iff $U=V\,R\,L$ for some $V\in\mathrm{Circ}_d$, some reflection layer $R$ and some local layer $L$. Thus $U=L_0R_1L_1\cdots R_dL_d$.
--
--   **Theorem.** For every $d\in\mathbb{N}$ and every complex $2^N\times2^N$ matrix $U$,
--
--   $$
--   U\in\mathrm{Circ}_d\ \Longrightarrow\ U^{*}\in\mathrm{Circ}_d ,
--   $$
--
--   where $U^{*}$ is the conjugate transpose of $U$.
--
--   Since all layers are unitary, $U^{*}=U^{-1}$, so the class of depth-$d$ normal-form circuits is closed under inversion. In the localization argument this allows an estimate proved for all depth-$d$ circuits to be applied to the time-reversed circuit $U^{*}$, which exchanges the roles of the initial and the final product projection.
--
--   **Formalization Note** The class $\mathrm{Circ}_d$ is the predicate `IsCircuit d` on `Operator N`, and $U^*$ is `star U`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Circuit.lean#L160-L173

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.IsCircuit.star_mem {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) :
    IsCircuit d (star U) := by sorry
