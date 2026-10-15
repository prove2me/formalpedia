-- Prove2me | Theorems.Thm_OAI_QAC_parity_trace_identity
-- name    : OAI.QAC.parity_trace_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:54:15.473966+00:00
-- url     : https://prove2.me/theorems/2e8b3804-e56c-4bbb-b49d-5e3b59ed7d5a
-- title:
--   Parity trace identity: flipped-input entries of $H_{\mathrm{in}}BH_{\mathrm{in}}$ sum to the parity-weighted diagonal of $B$
-- statement:
--   Let $n\le N$, with qubits $0,\dots,n-1$ the input qubits and the remaining qubits ancillas, and let $B$ be any complex matrix indexed by $\{0,1\}^N$. For $x\in\{0,1\}^n$ write:
--
--   - $\hat x\in\{0,1\}^N$ for the padded input ($\hat x_i=x_i$ for $i<n$, $\hat x_i=0$ for $i\ge n$);
--   - $\bar x\in\{0,1\}^N$ for $\hat x$ with all $n$ input bits flipped ($\bar x_i=1-x_i$ for $i<n$, $\bar x_i=0$ for $i\ge n$);
--   - $\operatorname{par}(x)=x_0+\dots+x_{n-1}\bmod 2$ for the parity of $x$.
--
--   Let $H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ be the Hadamard matrix and $H_{\mathrm{in}}=\bigotimes_{i}A_i$ with $A_i=H$ for $i<n$ and $A_i=I$ for $i\ge n$, the layer of Hadamard gates on the input qubits. Then
--
--   $$
--   \sum_{x\in\{0,1\}^n}\bigl(H_{\mathrm{in}}\,B\,H_{\mathrm{in}}\bigr)_{\bar x,\ \hat x}\;=\;\sum_{x\in\{0,1\}^n}(-1)^{\operatorname{par}(x)}\,B_{\hat x,\hat x}.
--   $$
--
--   This is the Fourier step of the parity lower bound, written as a trace identity: the correlation of the diagonal entries of $B$ on padded inputs with the parity character equals a sum of entries of $H_{\mathrm{in}}BH_{\mathrm{in}}$ that connect basis states differing in all $n$ input bits. Applied to $B=W^{\ast}PW$ for a circuit $W$ and an output measurement projection $P$, it shows that a circuit whose Hadamard-conjugated observable has only small entries between such far-apart states cannot correlate with parity.
--
--   **Formalization Note** $\bar x$ is `flipWord (inputSet n N) (inputWord x)`, $H_{\mathrm{in}}$ is `localMatrix (inputHadamard n N)`, and the sign $(-1)^{\operatorname{par}(x)}$ is the real number `bitSign (parity x)` cast to $\mathbb C$; the parity is computed in $\mathbb Z/2\mathbb Z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ParityTrace.lean#L70-L86

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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem OAI.QAC.parity_trace_identity {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    (∑ x : Word n, (localMatrix (inputHadamard n N)*B*localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)) =
    ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by sorry
