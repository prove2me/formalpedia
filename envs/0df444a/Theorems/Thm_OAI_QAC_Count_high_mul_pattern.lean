-- Prove2me | Theorems.Thm_OAI_QAC_Count_high_mul_pattern
-- name    : OAI.QAC.Count.high_mul_pattern
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:33:27.458099+00:00
-- url     : https://prove2.me/theorems/d7f5ee36-5bc1-4bc8-b2ab-931c0a1f1fff
-- title:
--   The high projection of the mismatch count fixes or annihilates each mismatch pattern
-- statement:
--   Let $M=(S,v)$ be a count on $N$ qubits: a set $S\subseteq\{0,\dots,N-1\}$ of qubits together with unit vectors $v_i\in\mathbb C^2$ for $i\in S$, and write $\Pi_i=|v_i\rangle\langle v_i|$. For a set $F$ of qubits let $P_M^F$ be the mismatch-pattern projection, the tensor product of $I-\Pi_i$ on $S\cap F$, of $\Pi_i$ on $S\setminus F$ and of $I$ off $S$. For $r\in\mathbb R$ let
--   $[\mathcal N_M\ge r]=\sum_{G\subseteq S,\ |G|\ge r}P_M^G$ be the high projection of the mismatch count.
--
--   If $F\subseteq S$ and $r\in\mathbb R$, then
--   $$
--   [\mathcal N_M\ge r]\,P_M^F=\begin{cases}P_M^F, & r\le |F|,\\ 0, & r>|F|.\end{cases}
--   $$
--
--   In other words, $[\mathcal N_M\ge r]$ acts on the range of $P_M^F$ as the identity if $|F|\ge r$ and as zero otherwise, as expected of the spectral projection of a mismatch count that takes the value $|F|$ on that range. This is the basic multiplication rule used to compare the high projections of a count and of its axis-flipped variants in the localization estimates for constant-depth circuits.
--
--   **Formalization Note** Operators are complex matrices indexed by $\{0,1\}^N\times\{0,1\}^N$. The high projection is `Count.high`, a sum over the powerset of the support with an if-then-else coefficient, and the hypothesis $F\subseteq S$ is `hF : F ⊆ M.support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Spectral.lean#L23-L36

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.Count.high_mul_pattern {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (r : ℝ) :
    M.high r * M.pattern F = if r ≤ (F.card : ℝ) then M.pattern F else 0 := by sorry
