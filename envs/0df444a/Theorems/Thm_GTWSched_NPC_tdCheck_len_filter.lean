-- Prove2me | Theorems.Thm_GTWSched_NPC_tdCheck_len_filter
-- name    : GTWSched.NPC.tdCheck_len_filter
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T21:31:01.170205+00:00
-- url     : https://prove2.me/theorems/7ce9164e-7362-4e65-88b2-17537f45139e
-- title:
--   Total discrepancy checker: polynomial-time length filter
-- statement:
--   Inputs of the checker are strings over the alphabet $\Sigma=\{\bot\}\cup\mathrm{BSym}\sqcup\mathrm{BSym}$ of the form
--
--   $$u=\mathrm{enc}(c)\,\bot\,\mathrm{enc}(d),$$
--
--   where $c=(c_0,c_1,\dots)$ is a list of integers written in binary (the instance part, tagged on the left) and $d=(d_0,d_1,\dots)$ is a list of natural numbers written in binary (the certificate part, tagged on the right). For a total discrepancy instance the instance part is $c=(N,k,M_1,\dots,M_N,l_1,\dots,l_N)$.
--
--   There is a structured multi-stack program (hence, by `stack_program_polytime`, a polynomial-time Turing machine) whose number of steps on an input $u$ is at most $|u|^K+K$ for a constant $K$, and which outputs $u$ itself if
--
--   1. $u=\mathrm{enc}(c)\,\bot\,\mathrm{enc}(d)$ for some integer list $c$ and natural-number list $d$,
--   2. every entry of $c$ is positive,
--   3. $|c| = 2+2c_0$, and
--   4. $|d| = 3c_0+1$,
--
--   and outputs the empty string otherwise.
--
--   This is the shape check of the certificate checker for the total discrepancy problem: it accepts exactly the well-formed pairs (instance code, certificate code) whose instance part has the shape $N,k,M_1,\dots,M_N,l_1,\dots,l_N$ with positive entries and whose certificate has $3N+1$ entries.
--
--   **Formalization Note** The program is a `CookPvsNP.StackProg` over the alphabet `Option (BSym ⊕ BSym)`; the input sits on stack `ki`, the output is read from stack `ko`. The certificate list is written with `encNats`, the instance list with `encInts`.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 336 (membership of the total discrepancy problem in NP, left there "as a simple exercise"); technical lemma of the polynomial-time certificate checker used in the proof of GTWSched.NPC.td_mem_NP

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

open CookPvsNP

namespace GTWSched.NPC

open ProjSchedTW.Complexity

/-- Length filter of the total-discrepancy certificate checker: a polynomial-time stack program
that keeps exactly the inputs `enc(c) ⊥ enc(d)` with positive entries `c = N, k, M₁, …, M_N,
l₁, …, l_N` (so `|c| = 2 + 2N`) and a certificate `d` of length `3N + 1`, and erases every other
input. -/
theorem tdCheck_len_filter : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          (∀ v ∈ c, 0 < v) ∧ c.length = 2 + 2 * (c.getD 0 0).toNat ∧
          d.length = 3 * (c.getD 0 0).toNat + 1) → s ko = u) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          (∀ v ∈ c, 0 < v) ∧ c.length = 2 + 2 * (c.getD 0 0).toNat ∧
          d.length = 3 * (c.getD 0 0).toNat + 1) → s ko = []) := by sorry

end GTWSched.NPC
