-- Prove2me | Theorems.Thm_GTWSched_NPC_tdCheck_cost_filter
-- name    : GTWSched.NPC.tdCheck_cost_filter
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T21:30:54.29492+00:00
-- url     : https://prove2.me/theorems/de94af50-7303-47f8-ac75-2172773afd45
-- title:
--   Total discrepancy checker: polynomial-time cost filter
-- statement:
--   Inputs of the checker are strings over the alphabet $\Sigma=\{\bot\}\cup\mathrm{BSym}\sqcup\mathrm{BSym}$ of the form
--
--   $$u=\mathrm{enc}(c)\,\bot\,\mathrm{enc}(d),$$
--
--   where $c=(c_0,c_1,\dots)$ is a list of integers written in binary (the instance part, tagged on the left) and $d=(d_0,d_1,\dots)$ is a list of natural numbers written in binary (the certificate part, tagged on the right). For a total discrepancy instance the instance part is $c=(N,k,M_1,\dots,M_N,l_1,\dots,l_N)$.
--
--   Let $N=\lfloor |d|/3\rfloor$ and read the certificate as $d=(P_{0}',t_1,h_1,P_1,\dots,t_N,h_N,P_N)$, i.e. $t_i=d_{3i-2}$, $h_i=d_{3i-1}$, $P_i=d_{3i}$ for $1\le i\le N$ and $P_0'=d_0$; write $P_{i-1}'=d_{3i-3}$ for the entry preceding $t_i$. Put $M_i=|c_{1+i}|$, $l_i=|c_{1+N+i}|$ and $k=|c_1|$. The cost conditions are
--
--   $$d_0=0,\qquad t_i+l_i=h_i,\qquad h_i+P_{i-1}'\le 2M_i+P_i,\qquad 2M_i+P_{i-1}'\le h_i+P_i\quad(1\le i\le N),\qquad d_{3N}\le 2k .$$
--
--   (Equivalently $P_i-P'_{i-1}\ge|h_i-2M_i|$, so the entries $P$ certify $\sum_i|h_i-2M_i|\le 2k$.) There is a structured multi-stack program running in at most $|u|^K+K$ steps that outputs the empty string on every input $u=\mathrm{enc}(c)\,\bot\,\mathrm{enc}(d)$ violating one of these conditions, and outputs $u$ unchanged on every other input (including inputs not of this form).
--
--   Here $t_i$ is a doubled starting time and $h_i=t_i+l_i$ the doubled midtime of task $i$, so the conditions say that the schedule with starting times $t_i/2$ has total discrepancy $\sum_i|h_i/2-M_i|\le k$; this is the cost check of the certificate checker for the total discrepancy problem.
--
--   **Formalization Note** Indices in Lean are 0-based: task $i\in\{0,\dots,N-1\}$ uses $d_{3i},d_{3i+1},d_{3i+2},d_{3i+3}$ and $c_{2+i}$, $c_{2+N+i}$. Absolute values `natAbs` of the instance entries are used so that the statement makes sense for every integer list; for well-formed instances these entries are positive.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 336 (membership of the total discrepancy problem in NP, left there "as a simple exercise"); technical lemma of the polynomial-time certificate checker used in the proof of GTWSched.NPC.td_mem_NP

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

open CookPvsNP

namespace GTWSched.NPC

open ProjSchedTW.Complexity

/-- Cost filter of the total-discrepancy certificate checker. With `N = |d| / 3`, the certificate
`d = P₋₁, t₁, h₁, P₁, …, t_N, h_N, P_N` lists doubled starting times `tᵢ`, doubled midtimes
`hᵢ = tᵢ + lᵢ` and partial bounds `Pᵢ` with `Pᵢ - Pᵢ₋₁ ≥ |hᵢ - 2Mᵢ|`, `P₋₁ = 0` and
`P_N ≤ 2k`. A polynomial-time stack program erases exactly the inputs `enc(c) ⊥ enc(d)` violating
one of these conditions and keeps every other input. -/
theorem tdCheck_cost_filter : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(d.getD 0 0 = 0 ∧
            (∀ i < d.length / 3,
              d.getD (3 * i + 1) 0 + (c.getD (2 + d.length / 3 + i) 0).natAbs =
                d.getD (3 * i + 2) 0 ∧
              d.getD (3 * i + 2) 0 + d.getD (3 * i) 0 ≤
                2 * (c.getD (2 + i) 0).natAbs + d.getD (3 * i + 3) 0 ∧
              2 * (c.getD (2 + i) 0).natAbs + d.getD (3 * i) 0 ≤
                d.getD (3 * i + 2) 0 + d.getD (3 * i + 3) 0) ∧
            d.getD (3 * (d.length / 3)) 0 ≤ 2 * (c.getD 1 0).natAbs)) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(d.getD 0 0 = 0 ∧
            (∀ i < d.length / 3,
              d.getD (3 * i + 1) 0 + (c.getD (2 + d.length / 3 + i) 0).natAbs =
                d.getD (3 * i + 2) 0 ∧
              d.getD (3 * i + 2) 0 + d.getD (3 * i) 0 ≤
                2 * (c.getD (2 + i) 0).natAbs + d.getD (3 * i + 3) 0 ∧
              2 * (c.getD (2 + i) 0).natAbs + d.getD (3 * i) 0 ≤
                d.getD (3 * i + 2) 0 + d.getD (3 * i + 3) 0) ∧
            d.getD (3 * (d.length / 3)) 0 ≤ 2 * (c.getD 1 0).natAbs)) → s ko = u) := by sorry

end GTWSched.NPC
