-- Prove2me | Theorems.Thm_OAI_QAC_sum_ancillaValid
-- name    : OAI.QAC.sum_ancillaValid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:51:34.66498+00:00
-- url     : https://prove2.me/theorems/9148df4e-e5ab-4730-9de4-73add9c31214
-- title:
--   Sums over ancilla-valid words are sums over padded inputs
-- statement:
--   Let $n\le N$ be natural numbers; think of qubits $0,\dots,n-1$ as input qubits and of qubits $n,\dots,N-1$ as ancillas. For $x\in\{0,1\}^n$ let $\hat x\in\{0,1\}^N$ be the padded input, $\hat x_i=x_i$ for $i<n$ and $\hat x_i=0$ for $n\le i\le N-1$. Call a word $z\in\{0,1\}^N$ ancilla-valid if $z_i=0$ for every $i$ with $n\le i\le N-1$. Then for every commutative additive monoid $A$ and every function $f:\{0,1\}^N\to A$,
--
--   $$
--   \sum_{\substack{z\in\{0,1\}^N\\ z\ \text{ancilla-valid}}} f(z)\;=\;\sum_{x\in\{0,1\}^n} f(\hat x).
--   $$
--
--   Equivalently, padding $x\mapsto\hat x$ is a bijection from the inputs onto the ancilla-valid words. The identity is the bookkeeping step that turns traces of $N$-qubit operators against the zero-ancilla projection into sums over the $2^n$ inputs; it is used twice in the parity trace identity.
--
--   **Formalization Note** The left side is the sum over all $z$ of `if ancillaValid n z then f z else 0`, and $\hat x$ is `inputWord x`. The hypothesis $n\le N$ guarantees that padding is injective (for $n>N$, `inputWord` would truncate).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean#L41-L57

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

theorem OAI.QAC.sum_ancillaValid {n N : ℕ} (hnN : n ≤ N) {α : Type*} [AddCommMonoid α]
    (f : Word N → α) :
    (∑ z : Word N, if ancillaValid n z then f z else 0) = ∑ x : Word n, f (inputWord x) := by sorry
