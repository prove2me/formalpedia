-- Prove2me | Theorems.Thm_HallReps_CDR_lemma_cdrMeet
-- name    : HallReps.CDR.lemma_cdrMeet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:08:23.833984+00:00
-- url     : https://prove2.me/theorems/ea656efe-d35e-42da-a54c-4ed3cd1be082
-- title:
--   Lemma, p. 27 — the sets represented by the meet R of all C.D.R.s contain between them exactly the elements of R
-- statement:
--   Let $T_i$ ($i \in I$) be a finite system of subsets of a set $S$, and let $a = (a_i)_{i \in I}$ be a C.D.R. of it. Let $R$ be the meet of all the C.D.R.s of the system, i.e. the set of elements of $S$ that occur as representatives in every C.D.R. Since $a$ is itself a C.D.R., every element of $R$ is some $a_i$; let
--   $$I_R = \{i \in I : a_i \in R\}$$
--   be the indices of the sets whose representative in $a$ lies in $R$ (in the paper, after renumbering, $R = \{a_1, \dots, a_\rho\}$ and these are the sets $T_1, \dots, T_\rho$). Then these $\rho = |I_R|$ sets contain between them exactly $\rho$ elements, namely the elements of $R$:
--   $$\bigcup_{i \in I_R} T_i = R \qquad\text{and}\qquad |R| = |I_R|.$$
--   The case $\rho = 0$ (that is, $R = \varnothing$) is included.
--
--   The lemma is the engine of Hall's inductive proof of Theorem 1: it says that the elements forced into every C.D.R. form a "tight" block of sets which can only be represented by those elements.
--
--   **Formalization Note.** The system is `T : ι → Set α` with `[Finite ι]`; the paper's silent renumbering "$R = a_1, \dots, a_\rho$; $T_1, \dots, T_\rho$" is encoded by the index set `{i | a i ∈ cdrMeet T}`. The count is stated in `ℕ∞` (`Set.encard` and `ENat.card`). The finiteness of the system is necessary: the paper's system (1) is finite.
-- source:
--   P. Hall, On representatives of subsets, J. London Math. Soc. 10 (1935), p. 27, Lemma (proof pp. 27–28)

import Mathlib
import Definitions.Def_HallReps_CDR_System

namespace HallReps.CDR

theorem lemma_cdrMeet {ι α : Type*} [Finite ι] (T : ι → Set α) (a : ι → α)
    (ha : IsCDR T a) :
    (⋃ (i : ι) (_ : a i ∈ cdrMeet T), T i) = cdrMeet T ∧
      (cdrMeet T).encard = ENat.card {i : ι // a i ∈ cdrMeet T} := by sorry

end HallReps.CDR
