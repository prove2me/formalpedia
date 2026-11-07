-- Prove2me | Theorems.Thm_GTWSched_NPC_tdCheck_overlap_filter
-- name    : GTWSched.NPC.tdCheck_overlap_filter
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T21:30:55.125296+00:00
-- url     : https://prove2.me/theorems/e2c1742c-a0b7-4aa9-a0a7-307903885f99
-- title:
--   Total discrepancy checker: polynomial-time overlap filter
-- statement:
--   Inputs of the checker are strings over the alphabet $\Sigma=\{\bot\}\cup\mathrm{BSym}\sqcup\mathrm{BSym}$ of the form
--
--   $$u=\mathrm{enc}(c)\,\bot\,\mathrm{enc}(d),$$
--
--   where $c=(c_0,c_1,\dots)$ is a list of integers written in binary (the instance part, tagged on the left) and $d=(d_0,d_1,\dots)$ is a list of natural numbers written in binary (the certificate part, tagged on the right). For a total discrepancy instance the instance part is $c=(N,k,M_1,\dots,M_N,l_1,\dots,l_N)$.
--
--   Let $N=\lfloor |d|/3\rfloor$, let $t_i=d_{3i+1}$ be the doubled starting time and $l_i=|c_{2+N+i}|$ the length of task $i$ ($0\le i<N$). The non-overlap condition is
--
--   $$\forall\, 0\le i<j<N:\qquad t_i+2l_i\le t_j\quad\text{or}\quad t_j+2l_j\le t_i .$$
--
--   There is a structured multi-stack program running in at most $|u|^K+K$ steps that outputs the empty string on every input $u=\mathrm{enc}(c)\,\bot\,\mathrm{enc}(d)$ violating this condition, and outputs $u$ unchanged on every other input (including inputs not of this form).
--
--   With starting times $t_i/2$ the condition says that the execution intervals $[t_i/2,t_i/2+l_i]$ of distinct tasks overlap at most in an endpoint, i.e. the certificate describes a one-processor schedule; this is the feasibility check of the certificate checker for the total discrepancy problem.
--
--   **Formalization Note** Absolute values `natAbs` of the instance entries are used so that the statement makes sense for every integer list; for well-formed instances these entries are positive.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 336 (membership of the total discrepancy problem in NP, left there "as a simple exercise"); technical lemma of the polynomial-time certificate checker used in the proof of GTWSched.NPC.td_mem_NP

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

open CookPvsNP

namespace GTWSched.NPC

open ProjSchedTW.Complexity

/-- Overlap filter of the total-discrepancy certificate checker. With `N = |d| / 3`, the doubled
starting time of task `i` is `tᵢ = d_{3i+1}` and its doubled length is `2lᵢ`, `lᵢ = |c_{2+N+i}|`.
A polynomial-time stack program erases exactly the inputs `enc(c) ⊥ enc(d)` in which two tasks
`i < j` overlap (neither `tᵢ + 2lᵢ ≤ tⱼ` nor `tⱼ + 2lⱼ ≤ tᵢ`) and keeps every other input. -/
theorem tdCheck_overlap_filter : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
            d.getD (3 * i + 1) 0 + 2 * (c.getD (2 + d.length / 3 + i) 0).natAbs ≤
                d.getD (3 * j + 1) 0 ∨
              d.getD (3 * j + 1) 0 + 2 * (c.getD (2 + d.length / 3 + j) 0).natAbs ≤
                d.getD (3 * i + 1) 0)) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
            d.getD (3 * i + 1) 0 + 2 * (c.getD (2 + d.length / 3 + i) 0).natAbs ≤
                d.getD (3 * j + 1) 0 ∨
              d.getD (3 * j + 1) 0 + 2 * (c.getD (2 + d.length / 3 + j) 0).natAbs ≤
                d.getD (3 * i + 1) 0)) → s ko = u) := by sorry

end GTWSched.NPC
