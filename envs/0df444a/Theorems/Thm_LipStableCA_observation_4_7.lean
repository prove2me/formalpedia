-- Prove2me | Theorems.Thm_LipStableCA_observation_4_7
-- name    : LipStableCA.observation_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:37.5746+00:00
-- url     : https://prove2.me/theorems/32b1cf01-9c8c-43ae-a244-b8d9f683f0fe
-- title:
--   Observation 4.7 — the selected allocation is determined by the maximum score
-- statement:
--   Fix a bidder $i$, a profile $v$ and a zero pattern $\mathcal B=\{B_1,\dots,B_R\}$. Let $U$ be the set of valid profiles $u$ with $u_{-i}=v_{-i}$ in which $u_i(B)>0$ exactly for $B\in\mathcal B$. For a vector of discounts $a$, let $c_B(a)$ be the largest discounted welfare of the other bidders among allocations giving $B$ to bidder $i$, let $c_0(a)=\max_{B\notin\mathcal B}c_B(a)$, and let the scores be $s_0(u,a)=c_0(a)$ and $s_j(u,a)=c_j(a)+a_{i,B_j}u_i(B_j)$. An allocation has index $j$ if it gives $B_j$ to bidder $i$, and index $0$ if it gives her a bundle outside $\mathcal B$; $J(u,a)$ is the index of the selected allocation $S^*(u,a)$. For every $a$ and every $u\in U$:
--
--   1. An allocation of index $k$ maximizes the discounted welfare at $u$ if and only if $s_k(u,a)$ is the maximum score at $u$ and the allocation attains $c_k(a)$.
--   2. The index $J(u,a)$ has the maximum score at $u$. Moreover, if the score of an index $j$ is larger than the scores of all the other indices at $u$, then $J(u,a)=j$.
--   3. $S^*(u,a)$ is the first allocation in the fixed order among the allocations of index $J(u,a)$ that attain $c_{J(u,a)}(a)$. In particular, for every $u'\in U$, if $J(u,a)=J(u',a)$, then $S^*(u,a)=S^*(u',a)$.
--
--   This reduces the change of the selected allocation to a change of a one-dimensional comparison of scores.
--
--   Differences from the source:
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
--   - encoding: indices $j\in\{0,1,\dots,R\}$ → the bundle $B_j$ itself (`some B`), and `none` for $0$; reason: the enumeration of $\mathcal B$ plays no role
--   - generalization: a vector of discounts (values in $[1-\epsilon,1]$, $a_{h,\emptyset}=1$) → every real array $a$; reason: the printed proof uses no property of the discounts; it specializes to every discount vector
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 4.7, p.16

import Definitions.Def_LipStableCA_discountIndex

namespace LipStableCA

/-- **Observation 4.7.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.16. **Formalization Note.** an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. the bundle `B_j` itself (`some B`), and `none` for `0`: the enumeration of `𝓑` plays no role. every real array `a`: the printed proof uses no property of the discounts; it specializes to every discount vector. -/
theorem observation_4_7 {n m : ℕ} (ord : LinearOrder (Alloc n m)) (i : Fin n) (v : Profile n m)
    (𝓑 : Finset (Finset (Fin m))) (a : Fin n → Finset (Fin m) → ℝ) (u : Profile n m)
    (hu : InPattern v i 𝓑 u) :
    (∀ T : Alloc n m, (∀ T', discountedWelfare a u T' ≤ discountedWelfare a u T) ↔
      (∀ k, IsIndex 𝓑 k → score a v i 𝓑 u k ≤ score a v i 𝓑 u (allocIndex i 𝓑 T)) ∧
        Attains a v i 𝓑 T (allocIndex i 𝓑 T)) ∧
    (∀ k, IsIndex 𝓑 k → score a v i 𝓑 u k ≤ score a v i 𝓑 u (selectedIndex ord i 𝓑 a u)) ∧
    (∀ j, IsIndex 𝓑 j → (∀ k, IsIndex 𝓑 k → k ≠ j → score a v i 𝓑 u k < score a v i 𝓑 u j) →
      selectedIndex ord i 𝓑 a u = j) ∧
    (Attains a v i 𝓑 (selected ord a u) (selectedIndex ord i 𝓑 a u) ∧
      ∀ T : Alloc n m, allocIndex i 𝓑 T = selectedIndex ord i 𝓑 a u →
        Attains a v i 𝓑 T (selectedIndex ord i 𝓑 a u) → ord.le (selected ord a u) T) ∧
    (∀ u' : Profile n m, InPattern v i 𝓑 u' →
      selectedIndex ord i 𝓑 a u = selectedIndex ord i 𝓑 a u' → selected ord a u = selected ord a u') := by sorry

end LipStableCA
