-- Prove2me | Theorems.Thm_OAI_QAC_Count_pattern_mul
-- name    : OAI.QAC.Count.pattern_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:31:44.544979+00:00
-- url     : https://prove2.me/theorems/30d18a85-7bdc-4194-92a2-d244f63a6dea
-- title:
--   The mismatch-pattern projections of a count are mutually orthogonal
-- statement:
--   Let $M$ be a count on $N$ qubits: a support $S\subseteq[N]=\{0,\dots,N-1\}$ together with one-qubit vectors $v_i\in\mathbb{C}^2$ that are unit vectors for $i\in S$. Write $P_i=|v_i\rangle\langle v_i|$. For $F\subseteq[N]$ the pattern projection of $M$ is the operator on $(\mathbb{C}^2)^{\otimes N}$
--
--   $$
--   \Pi^M_F=\bigotimes_{i\in[N]}Q^F_i,\qquad Q^F_i=\begin{cases}I-P_i,&i\in S\cap F,\\ P_i,&i\in S\setminus F,\\ I,&i\notin S,\end{cases}
--   $$
--
--   which, for $F\subseteq S$, projects onto the states whose set of qubits in $S$ disagreeing with the reference vectors $v_i$ is exactly $F$.
--
--   **Theorem.** For all subsets $F,G\subseteq S$,
--
--   $$
--   \Pi^M_F\,\Pi^M_G=\begin{cases}\Pi^M_F,&F=G,\\ 0,&F\ne G.\end{cases}
--   $$
--
--   Together with $\sum_{F\subseteq S}\Pi^M_F=I$, this says that the pattern projections form an orthogonal resolution of the identity indexed by the subsets of $S$. It is the basis of the spectral calculus of the mismatch count: it shows, for example, that $\Pi^M_{\ge r}=\sum_{F\subseteq S,\,|F|\ge r}\Pi^M_F$ is a projection, and that real functions of the count act diagonally on this resolution.
--
--   **Formalization Note** The pattern projection is `M.pattern F`, and the right-hand side is written `if F = G then M.pattern F else 0`. The hypotheses `F ⊆ M.support` and `G ⊆ M.support` are explicit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean#L108-L128

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.Count.pattern_mul {N : ℕ} (M : Count N) {F G : Finset (Fin N)}
    (hF : F ⊆ M.support) (hG : G ⊆ M.support) :
    M.pattern F * M.pattern G = if F = G then M.pattern F else 0 := by sorry
