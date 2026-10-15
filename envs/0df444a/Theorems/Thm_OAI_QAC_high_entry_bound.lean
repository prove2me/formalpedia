-- Prove2me | Theorems.Thm_OAI_QAC_high_entry_bound
-- name    : OAI.QAC.high_entry_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:51:01.926755+00:00
-- url     : https://prove2.me/theorems/1bee2f1f-f7e6-48fd-84af-bab915dd9946
-- title:
--   Entries between basis states at Hamming distance at least $r$ are bounded by a high-mismatch projection norm
-- statement:
--   Let $N\in\mathbb N$ and let $B$ be any complex matrix whose rows and columns are indexed by $\{0,1\}^N$ (an operator on $N$ qubits). Fix a word $z\in\{0,1\}^N$, a set of qubits $F\subseteq\{0,\dots,N-1\}$ and a real number $r$ with $r\le|F|$. Write $z\oplus\mathbf 1_F$ for the word obtained from $z$ by flipping the bits in $F$.
--
--   Let $M_z$ be the computational count of $z$: its support is all of $\{0,\dots,N-1\}$ and its axis on qubit $i$ is the basis vector $|z_i\rangle$. Its zero-mismatch projection is $P^0_{M_z}=|z\rangle\langle z|$, and its high projection $[\mathcal N_{M_z}\ge r]=\sum_{G\,:\,r\le|G|}P^G_{M_z}$ is the orthogonal projection onto the span of the basis vectors $|y\rangle$ whose Hamming distance from $z$ is at least $r$. Then
--
--   $$
--   \bigl|B_{z\oplus\mathbf 1_F,\ z}\bigr|\ \le\ \bigl\|\,[\mathcal N_{M_z}\ge r]\;B\;P^0_{M_z}\bigr\|,
--   $$
--
--   where on the right $\|\cdot\|$ is the operator norm induced by the Euclidean norm on $\mathbb C^{\{0,1\}^N}$.
--
--   The lemma converts information about how far $B$ can move the basis state $|z\rangle$ in Hamming distance into a bound on an individual matrix entry. In the parity lower bound it is applied with $F$ the set of input qubits (so $|F|=n$) and $r=N^t\le n$: the localization theorem bounds the right-hand side, and therefore the entries of the Hadamard-conjugated measurement operator that connect a padded input with its completely flipped version.
--
--   **Formalization Note** $P^0_{M_z}$ is `(computationalCount z).zero` and the high projection is `(computationalCount z).high r`, defined as the sum of the pattern projections over subsets $G$ of the support with $r\le|G|$. The operator norm is the scoped instance `Matrix.Norms.L2Operator`, and the left side is the complex modulus of the entry. There is no sign condition on $r$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Computational.lean#L100-L117

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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem OAI.QAC.high_entry_bound {N : ℕ} (B : Operator N) (z : Word N) (F : Finset (Fin N))
    {r : ℝ} (hr : r ≤ (F.card:ℝ)) :
    ‖B (flipWord F z) z‖ ≤ ‖(computationalCount z).high r*B*(computationalCount z).zero‖ := by sorry
