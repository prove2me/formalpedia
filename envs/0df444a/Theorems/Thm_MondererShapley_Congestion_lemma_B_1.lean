-- Prove2me | Theorems.Thm_MondererShapley_Congestion_lemma_B_1
-- name    : MondererShapley.Congestion.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:54.143033+00:00
-- url     : https://prove2.me/theorems/3a32443d-0ff7-41f3-ad3f-4192e230b97a
-- title:
--   Lemma B.1 — congestion payoffs decomposed by the number of users of each facility
-- statement:
--   Let $C$ be a congestion game with players $N = \{1, \dots, n\}$, facilities $M$, strategy sets $\Sigma^i$ and facility payoffs $c_j$, and payoffs $v^i(A) = \sum_{j\in A^i} c_j(\sigma_j(A))$ as in (3.1). For $A = (A^1, \dots, A^n) \in \Sigma$ and $S \subseteq N$ write $A(S) = \bigcup_{k\in S} A^k$, $A(-S) = A(S^c)$, and $A(i) = A(\{i\})$, $A(-i) = A(-\{i\})$. For $x \in \mathbb{R}^M$ and $B \subseteq M$ write $x(B) = \sum_{j\in B} x(j)$. For every $r \in \{1, \dots, n\}$ define $x^r \in \mathbb{R}^M$ by $x^r(j) = c_j(r)$.
--
--   Then for every $i \in N$ and every $A \in \Sigma$,
--
--   $$v^i(A) = x^1\big(A(i)\cap A(-i)^c\big) + x^2\Big(\bigcup_{k\neq i}\big[A(i)\cap A(k)\cap A(-\{i,k\})^c\big]\Big) + \cdots + x^n\Big(\bigcap_{k\in N} A(k)\Big). \tag{B.1}$$
--
--   The $r$-th term is $x^r$ evaluated on the set of facilities used by player $i$ together with exactly $r-1$ other players, namely $\bigcup_{S \ni i,\ |S| = r}\big[\bigcap_{k\in S} A(k) \cap A(-S)^c\big]$. The lemma rewrites a congestion game as a sum of "level" contributions, which is the form in which the proof of Theorem 3.2 builds a congestion game with prescribed payoffs.
--
--   **Formalization Note.** The page prints $x^r(j) = c_j(m)$; $m$ is the number of facilities, and the lemma "follows from (3.1)" only with $c_j(r)$, so the misprint is corrected. The "$\cdots$" is read as the general term above, whose cases $r = 1, 2, n$ are the printed ones; $n$ is `Fintype.card ι`. The congestion game is the published model with $c_j(r)$ = `G.latency j r`.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 139 (PDF p. 16), Lemma B.1, (B.1)

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_MondererShapley_Congestion_congestionPayoff

open CongestionPoA.AsymSum

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), p. 139, Lemma B.1, (B.1): in a congestion game, with
`x^r(j) = c_j(r)`, every payoff decomposes by the number of users of each facility:
`vⁱ(A) = x¹(A(i) ∩ A(−i)^c) + x²(∪_{k≠i}[A(i) ∩ A(k) ∩ A(−{i,k})^c]) + ⋯ + xⁿ(∩_{k∈N} A(k))`,
where `A(S) = ∪_{k∈S} Aᵏ` and `A(−S) = A(Sᶜ)`.

**Formalization Note.** The printed `x^r(j) = c_j(m)` is a misprint for `c_j(r)`. The `r`-th term is
read as `x^r(∪_{S ∋ i, |S| = r} [∩_{k∈S} A(k) ∩ A(−S)^c])`, whose cases `r = 1, 2, n` are the printed
ones; `n = Fintype.card ι`. -/
theorem lemma_B_1 {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (G : CongestionGame ι M) (i : ι) (A : ∀ k, ↥(G.strategies k)) :
    congestionPayoff G i A =
      ∑ r ∈ Finset.Icc 1 (Fintype.card ι),
        ∑ j ∈ Finset.univ.filter (fun j : M => ∃ S : Finset ι, i ∈ S ∧ S.card = r ∧
            (∀ k ∈ S, j ∈ (A k : Finset M)) ∧ ∀ k ∉ S, j ∉ (A k : Finset M)),
          G.latency j r := by sorry

end MondererShapley.Congestion
