-- Prove2me | Theorems.Thm_OAI_QAC_Count_low_propagation_bound
-- name    : OAI.QAC.Count.low_propagation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:36:45.57216+00:00
-- url     : https://prove2.me/theorems/2e8d36d5-0d74-4e86-8153-b5af8ba7dbf7
-- title:
--   Transition bounds from zero-mismatch states propagate to the low-mismatch subspace
-- statement:
--   Fix $N\ge1$ and an $N$-qubit operator $B$, i.e. a complex matrix indexed by $\{0,1\}^N$; norms are operator norms for the Euclidean norm. For a count $K$ on $N$ qubits (a support $S_K$ with unit vectors $v_i\in\mathbb C^2$, $i\in S_K$) let $P_K^0=\bigotimes_{i\in S_K}|v_i\rangle\langle v_i|\otimes I$ be its zero-mismatch projection, $[\mathcal N_K\ge x]$ the spectral projection of its mismatch count onto the values at least $x$, and $[\mathcal N_K<x]=I-[\mathcal N_K\ge x]$.
--
--   Let $r,q,R,\delta\in\mathbb R$ with $\delta\ge0$ and $q+r\le R$, and assume that
--   $$\bigl\|[\mathcal N_K\ge q]\,B\,P_K^0\bigr\|\le\delta\qquad\text{for every count }K\text{ on }N\text{ qubits.}$$
--   Then every count $M$ on $N$ qubits satisfies
--   $$
--   \bigl\|[\mathcal N_M\ge R]\,B\,[\mathcal N_M<r]\bigr\|\le (N+1)^{\lceil r\rceil_+ +1}\,\delta,
--   $$
--   where $\lceil r\rceil_+$ is the least natural number that is at least $r$ (it equals $0$ when $r\le0$).
--
--   So a uniform bound on transitions that start in a zero-mismatch product state and end with at least $q$ mismatches implies a bound on transitions that start anywhere in the subspace with fewer than $r$ mismatches and end with at least $q+r$ mismatches, with a loss of order $N^{r}$. In the localization induction it is applied with $B=UP_D^0U^{*}$ for a circuit $U$ and $r=N^a$; the loss $(N+1)^{\lceil N^a\rceil_++1}=e^{O(N^a\log N)}$ is then absorbed by an exponentially small $\delta$.
--
--   **Formalization Note** $\lceil r\rceil_+$ is `Nat.ceil r` (written `⌈r⌉₊`), so the exponent is a natural number. The hypothesis quantifies over all `K : Count N`, and the low projection is `Count.low`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Transition.lean#L129-L144

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.Count.low_propagation_bound {N : ℕ} (M : Count N) (B : Operator N)
    {r q R δ : ℝ} (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hrq : q + r ≤ R)
    (hB : ∀ K : Count N, ‖K.high q * B * K.zero‖ ≤ δ) :
    ‖M.high R * B * M.low r‖ ≤ (N+1:ℝ)^(⌈r⌉₊+1) * δ := by sorry
