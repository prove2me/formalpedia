-- Prove2me | Theorems.Thm_OAI_QAC_ancillaProjection_diagonal
-- name    : OAI.QAC.ancillaProjection_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:53:05.968488+00:00
-- url     : https://prove2.me/theorems/899f9e8b-e7d6-4246-82f4-4ca0499f6419
-- title:
--   The zero-ancilla projection is diagonal in the computational basis
-- statement:
--   Let $n,N\in\mathbb N$ (no relation between them is assumed). The ancilla projection on $N$ qubits is the tensor product
--
--   $$
--   \Pi_{\mathrm{anc}}=\bigotimes_{i=0}^{N-1}A_i,\qquad A_i=\begin{cases}I, & i<n,\\ |0\rangle\langle0|, & i\ge n,\end{cases}
--   $$
--
--   which leaves the first $n$ qubits untouched and projects every other qubit onto $|0\rangle$. The theorem states that, in the computational basis indexed by $\{0,1\}^N$, $\Pi_{\mathrm{anc}}$ is the diagonal matrix
--
--   $$
--   (\Pi_{\mathrm{anc}})_{z,w}=\begin{cases}1, & z=w\ \text{and}\ z_i=0\ \text{for every}\ i\ \text{with}\ n\le i\le N-1,\\ 0, & \text{otherwise}.\end{cases}
--   $$
--
--   In other words, $\Pi_{\mathrm{anc}}=\operatorname{diag}(\mathbf 1_V)$, where $V$ is the set of ancilla-valid words; when $n\ge N$ every word is ancilla-valid and $\Pi_{\mathrm{anc}}=I$.
--
--   This diagonal form makes products and traces involving $\Pi_{\mathrm{anc}}$ computable entrywise: the diagonal of $\Pi_{\mathrm{anc}}C$ is the diagonal of $C$ restricted to ancilla-valid words, which then become sums over padded inputs. This is how the initialization of the ancillas to $|0\rangle$ enters the trace form of the parity identity.
--
--   **Formalization Note** $\Pi_{\mathrm{anc}}$ is `ancillaProjection n N`, the factor $|0\rangle\langle0|$ is `rankOne (basisVector 0)`, and ancilla validity is the decidable predicate `ancillaValid n z`; the right side is `Matrix.diagonal` of the corresponding $0/1$ indicator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean#L62-L81

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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem OAI.QAC.ancillaProjection_diagonal (n N : ℕ) :
    ancillaProjection n N = Matrix.diagonal (fun z => if ancillaValid n z then 1 else 0) := by sorry
