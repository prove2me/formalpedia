-- Prove2me | Theorems.Thm_OAI_QAC_small_support_layer_bound
-- name    : OAI.QAC.small_support_layer_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:39:25.386594+00:00
-- url     : https://prove2.me/theorems/eef04ac4-1e26-415e-9c97-4b6c137faa5d
-- title:
--   Passing one reflection layer and one local layer costs a factor $9^{|\operatorname{supp}A|}$
-- statement:
--   Work with $N$-qubit operators (complex matrices indexed by $\{0,1\}^N$, with the operator norm for the Euclidean norm) and write $\operatorname{conj}_W(X)=WXW^{*}$. For a count $K$ on $N$ qubits let $P_K^0$ be its zero-mismatch product projection, $\operatorname{supp}K$ its support, and $[\mathcal N_K\ge x]$, $[\mathcal N_K<x]=I-[\mathcal N_K\ge x]$ the spectral projections of its mismatch count.
--
--   Let $V$ be a unitary $N$-qubit operator, let $R=\prod_{j}(I-2P^0_{D_j})$ be the matrix of a reflection layer (counts $D_1,\dots,D_m$ with pairwise disjoint supports), let $L=\bigotimes_iL_i$ be the matrix of a local layer of one-qubit unitaries, let $M$ and $A$ be counts, and let $r,r_1,r_2,\delta\in\mathbb R$ with $\delta\ge0$. Assume that for every count $D$ on $N$ qubits
--   $$
--   \begin{aligned}
--   \bigl\|[\mathcal N_M\ge r_1]\operatorname{conj}_V(P_D^0)\,P_M^0\bigr\|&\le\delta,\\
--   \bigl\|[\mathcal N_M\ge r_2]\operatorname{conj}_V(P_D^0)\,[\mathcal N_M<r_1]\bigr\|&\le\delta,\\
--   \bigl\|[\mathcal N_M\ge r]\operatorname{conj}_V(P_D^0)\,[\mathcal N_M<r_2]\bigr\|&\le\delta.
--   \end{aligned}
--   $$
--   Then
--   $$
--   \bigl\|[\mathcal N_M\ge r]\operatorname{conj}_{VRL}(P_A^0)\,P_M^0\bigr\|\le 9^{|\operatorname{supp}A|}\cdot3\delta .
--   $$
--
--   This is the depth step for product projections of small support: transition bounds for the shallower circuit $V$, valid for all product projections at three thresholds, yield a transition bound for the deeper circuit $VRL$ applied to $P_A^0$, with a loss that is exponential only in the support size of $A$. When $|\operatorname{supp}A|\le N^u$ and $\delta=e^{-N^v}$ with $u<v$, this loss is negligible.
--
--   **Formalization Note** The circuit is the matrix product `V * reflectionMatrix R * localMatrix L`. The thresholds $r,r_1,r_2$ are arbitrary reals; no ordering between them is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean#L186-L210

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.small_support_layer_bound {N : ℕ} (V : Operator N) (hV : V ∈ unitary (Operator N))
    (R : ReflectionLayer N) (L : LocalLayer N) (M A : Count N) {r r₁ r₂ δ : ℝ} (hδ : 0 ≤ δ)
    (h₁ : ∀ D : Count N, ‖M.high r₁*conjugate V D.zero*M.zero‖ ≤ δ)
    (h₂ : ∀ D : Count N, ‖M.high r₂*conjugate V D.zero*M.low r₁‖ ≤ δ)
    (h₃ : ∀ D : Count N, ‖M.high r*conjugate V D.zero*M.low r₂‖ ≤ δ) :
    ‖M.high r*conjugate (V*reflectionMatrix R*localMatrix L) A.zero*M.zero‖ ≤
      (9:ℝ)^A.support.card*(3*δ) := by sorry
