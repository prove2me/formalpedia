-- Prove2me | Theorems.Thm_GreenTao_varnavides_set_count
-- name    : GreenTao.varnavides_set_count
-- status  : Open
-- author  : @davidnet
-- created : 2026-09-06T02:15:17.272866+00:00
-- url     : https://prove2.me/theorems/4c8c5516-a1da-4d48-95e6-3e72d34e0c47
-- title:
--   Varnavides: positive density gives quadratically many progressions
-- statement:
--   Fix an integer $k\ge3$ and a real density $0<\delta\le1$. There are constants $c>0$ and $B\in\mathbb N$ such that, for every prime $m\ge B$ and every subset $A\subseteq\mathbb Z/m\mathbb Z$ with $|A|\ge\delta m$,
--
--   $$\frac1{m^2}\sum_{x,r\in\mathbb Z/m\mathbb Z}\prod_{j=0}^{k-1}\mathbf 1_A(x+jr)\ge c.$$
--
--   The constants depend only on $k$ and $\delta$, not on $m$ or $A$. The count includes zero common differences and counts ordered pairs $(x,r)$. This is the set-valued Varnavides counting form of Szemerédi's theorem, which strengthens existence of one progression to a positive proportion of all pairs. It is a reusable combinatorial input for weighted and relative versions of Szemerédi's theorem.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §2, Proposition 2.3 and the subsequent Varnavides discussion, specializing the bounded function to the indicator of a set; absorb the vanishing error into a smaller positive constant.

import Definitions.Def_GreenTao_Pseudorandom

theorem GreenTao.varnavides_set_count
    (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ,
      ∀ (m : ℕ+) (_ : Nat.Prime (m : ℕ)) (_ : B ≤ (m : ℕ))
        (A : Finset (ZMod (m : ℕ))),
        δ * (m : ℝ) ≤ (A.card : ℝ) →
        c ≤ GreenTao.apAvg k (fun x => if x ∈ A then 1 else 0) := by sorry
