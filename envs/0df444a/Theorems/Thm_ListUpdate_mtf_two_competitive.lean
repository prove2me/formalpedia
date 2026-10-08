-- Prove2me | Theorems.Thm_ListUpdate_mtf_two_competitive
-- name    : ListUpdate.mtf_two_competitive
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:36:25.440409+00:00
-- url     : https://prove2.me/theorems/ec4c8732-7bf0-402d-822b-4c510d540bd7
-- title:
--   Sleator–Tarjan: move-to-front is $2$-competitive for list accessing
-- statement:
--   **Move-to-front is 2-competitive for list accessing** (Sleator–Tarjan, 1985).
--
--   *The list accessing problem.* A set of distinct items is stored in a linear list. A request names one of the items; serving it by accessing the item that is currently in position $i$ (positions counted from $1$ at the front) costs $i$. Immediately after an access, the accessed item may be moved to any position closer to the front at no cost; each position it advances counts as one *free exchange*. Any other swap of two adjacent items is a *paid exchange* and costs $1$. For an algorithm $A$ and a request sequence $s$ write
--
--   1. $C_A(s)$ for the total cost of the accesses (paid exchanges not included),
--   2. $X_A(s)$ for the number of paid exchanges, and
--   3. $F_A(s)$ for the number of free exchanges.
--
--   The *move-to-front* rule $\mathrm{MTF}$ serves each request by moving the accessed item to the front of the list, and makes no paid exchanges.
--
--   **Theorem.** Let $L$ be a list of distinct items and let $s=(x_1,\dots,x_m)$ be a sequence of $m$ requests, each naming an item of $L$. Let $A$ be any algorithm, online or offline, that serves $s$ starting from the list $L$, and let $\mathrm{MTF}$ serve $s$ starting from the same list $L$. Then
--
--   $$
--   C_{\mathrm{MTF}}(s)\le 2\,C_A(s)+X_A(s)-F_A(s)-m .
--   $$
--
--   Since the total cost of $A$ is $C_A(s)+X_A(s)$ and $F_A(s)\ge 0$, it follows that $C_{\mathrm{MTF}}(s)\le 2\,(C_A(s)+X_A(s))-m$: move-to-front never pays more than twice the cost of any algorithm, even one that knows the whole request sequence in advance. This is the result that founded the competitive analysis of online algorithms.
--
--   **Formalization Note** The inequality is stated with the subtracted terms moved to the left, $C_{\mathrm{MTF}}+F_A+m\le 2C_A+X_A$, to avoid truncated subtraction in $\mathbb N$. Lists are Lean `List α` with `L.Nodup`, and the requests are `req : Fin m → α` with every `req t ∈ L`. Positions in Lean are $0$-based (`List.idxOf`), so an access costs `idxOf + 1`. The run of $\mathrm{MTF}$ is the sequence of lists $M_0=L$, $M_{t+1}=x_t$ followed by $M_t$ with $x_t$ erased. Algorithm $A$ is described, for each request $t$, by the list `paid t` of the paid exchanges it performs before that access (an entry $p$ swaps the items at $0$-based positions $p$ and $p+1$; an entry with $p+1\ge |L|$ swaps nothing but is still charged) and by the $0$-based position `dest t` to which it then moves the accessed item, which must be at most the item's current position; $B_t$ is $A$'s list at the moment of the $t$-th access and $A_{t+1}$ its list after the free move. Paid exchanges made after the last access only increase $X_A$, so performing all paid exchanges before accesses loses no generality. Sleator and Tarjan state Theorem 1 for sequences of accesses, insertions and deletions starting from the empty list; this is the static, access-only version in which both algorithms start from the same list, the setting of Borodin and El-Yaniv, Chapter 1.
-- source:
--   D. D. Sleator and R. E. Tarjan, Amortized efficiency of list update and paging rules, Communications of the ACM 28(2) (1985) 202–208, Theorem 1 (C_MF(s) ≤ 2C_A(s) + X_A(s) − F_A(s) − m), here in its static access-only form with a common initial list; see also A. Borodin and R. El-Yaniv, Online Computation and Competitive Analysis, Cambridge University Press 1998, Chapter 1, Theorem 1.1.

import Mathlib

namespace ListUpdate

/-- **Sleator–Tarjan (1985), Theorem 1** (static list accessing, both algorithms starting
from the same list). Move-to-front versus an arbitrary (possibly offline) algorithm `A`:
`C_MTF(s) + F_A(s) + m ≤ 2 C_A(s) + X_A(s)`, i.e. `C_MTF ≤ 2 C_A + X_A - F_A - m`.

* `L` is the common initial list of distinct items, `req t` the `t`-th of `m` requests.
* `M t` is move-to-front's list before request `t`.
* `A t` is algorithm `A`'s list before request `t`; `A` first performs the paid exchanges
  `paid t` (an entry `p` swaps the items at 0-based positions `p` and `p + 1`), giving the
  list `B t` on which the access is made, and then moves the accessed item forward to
  the 0-based position `dest t` by free exchanges.
* Accessing the item at 0-based index `i` costs `i + 1`. -/
theorem mtf_two_competitive {α : Type*} [DecidableEq α]
    (L : List α) (hL : L.Nodup) (m : ℕ) (req : Fin m → α) (hreq : ∀ t, req t ∈ L)
    (M : Fin (m + 1) → List α) (hM0 : M 0 = L)
    (hM : ∀ t : Fin m, M t.succ = req t :: (M t.castSucc).erase (req t))
    (paid : Fin m → List ℕ) (dest : Fin m → ℕ)
    (A : Fin (m + 1) → List α) (B : Fin m → List α) (hA0 : A 0 = L)
    (hB : ∀ t : Fin m, B t = (paid t).foldl
      (fun (l : List α) (p : ℕ) => l.take p ++ ((l.drop p).take 2).reverse ++ l.drop (p + 2))
      (A t.castSucc))
    (hdest : ∀ t : Fin m, dest t ≤ (B t).idxOf (req t))
    (hA : ∀ t : Fin m, A t.succ = ((B t).erase (req t)).insertIdx (dest t) (req t)) :
    (∑ t, ((M t.castSucc).idxOf (req t) + 1)) + (∑ t, ((B t).idxOf (req t) - dest t)) + m ≤
      2 * (∑ t, ((B t).idxOf (req t) + 1)) + ∑ t, (paid t).length := by
  sorry

end ListUpdate
