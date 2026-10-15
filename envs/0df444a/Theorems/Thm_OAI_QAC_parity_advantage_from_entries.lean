-- Prove2me | Theorems.Thm_OAI_QAC_parity_advantage_from_entries
-- name    : OAI.QAC.parity_advantage_from_entries
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:56:41.584632+00:00
-- url     : https://prove2.me/theorems/f7365a71-db08-497d-a3a7-d9d5b7cec62f
-- title:
--   A parity advantage $\varepsilon$ forces a flipped-input entry of size at least $\varepsilon$
-- statement:
--   Let $1\le n\le N$, with qubits $0,\dots,n-1$ carrying the input and the other qubits ancillas initialized to $0$. Let $W$ be a unitary $2^N\times2^N$ matrix indexed by $\{0,1\}^N$, let $o\in\{0,\dots,N-1\}$ be an output qubit, and let $\varepsilon,\delta\in\mathbb R$. For $x\in\{0,1\}^n$ let $\hat x$ be the padded input, $\bar x$ the word $\hat x$ with its $n$ input bits flipped, and $\operatorname{par}(x)=x_0+\dots+x_{n-1}\bmod2$. The success probability of $W$ on $x$ is
--
--   $$
--   \mathrm{succ}(W,o,x)=\sum_{\substack{y\in\{0,1\}^N\\ y_o=\operatorname{par}(x)}}\bigl|W_{y,\hat x}\bigr|^2,
--   $$
--
--   the probability that measuring qubit $o$ of $W|\hat x\rangle$ yields $\operatorname{par}(x)$, with all other qubits summed out. Let $P_o=|0\rangle\langle0|_o\otimes I_{\mathrm{rest}}$ be the projection onto outcome $0$ on qubit $o$, and $H_{\mathrm{in}}$ the layer of Hadamard gates on the input qubits. Assume
--
--   1. $\mathrm{succ}(W,o,x)\ge\tfrac12+\varepsilon$ for every $x\in\{0,1\}^n$, and
--   2. $\bigl|\bigl(H_{\mathrm{in}}\,W^{\ast}P_oW\,H_{\mathrm{in}}\bigr)_{\bar x,\ \hat x}\bigr|\le\delta$ for every $x\in\{0,1\}^n$.
--
--   Then
--
--   $$
--   \varepsilon\le\delta .
--   $$
--
--   Thus a uniform advantage $\varepsilon$ over random guessing in computing parity forces at least one entry of the Hadamard-conjugated measurement observable, between a padded input and its fully flipped version, to have modulus at least $\varepsilon$. No cleanliness condition on the final state of the non-output qubits is imposed. In the parity lower bound these entries are shown to be exponentially small for constant-depth circuits on polynomially many qubits, which yields the contradiction.
--
--   **Formalization Note** Unitarity is membership of $W$ in `unitary (Operator N)`, $P_o$ is `(outputZeroCount out).zero`, $H_{\mathrm{in}}$ is `localMatrix (inputHadamard n N)`, and $\mathrm{succ}(W,o,x)$ is `successProbability W out x`. The flipped word $\bar x$ is `flipWord (inputSet n N) (inputWord x)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Measurement.lean#L78-L104

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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Measurement

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem OAI.QAC.parity_advantage_from_entries {n N : ℕ} (hn : 0<n) (hnN : n ≤ N)
    (W : Operator N) (hW : W ∈ unitary (Operator N)) (out : Fin N) {ε δ : ℝ}
    (hsuccess : ∀ x : Word n, 1/2+ε ≤ successProbability W out x)
    (hentry : ∀ x : Word n,
      ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
        localMatrix (inputHadamard n N)) (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ δ) :
    ε ≤ δ := by sorry
