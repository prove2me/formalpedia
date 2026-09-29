-- Prove2me | Theorems.Thm_GreenTao_relative_szemeredi
-- name    : GreenTao.relative_szemeredi
-- status  : Open
-- author  : @davidnet
-- created : 2026-09-06T01:25:03.424711+00:00
-- url     : https://prove2.me/theorems/e4c63a88-afaa-41ca-853a-934c2bf5f2c3
-- title:
--   Relative Szemerédi: positive weighted progression density
-- statement:
--   Fix an integer $k\ge3$. Let $M_n$ be prime moduli tending to infinity and let $\nu_n$ be a $k$-pseudorandom family on $\mathbb Z/M_n\mathbb Z$ in the sense of Green–Tao Definitions 3.1–3.3. Let $f_n$ be real functions satisfying $0\le f_n\le\nu_n$ pointwise. Suppose that for some fixed $0<\delta\le1$, their means are eventually at least $\delta$. Then
--
--   $$\exists c>0\quad\forall n\text{ sufficiently large},\qquad \mathbb E_{x,r\in\mathbb Z/M_n\mathbb Z}\prod_{j=0}^{k-1}f_n(x+jr)\ge c.$$
--
--   This is the positive lower bound consequence of Theorem 3.5. The average includes progressions of zero common difference. The statement applies to any dominated family and does not assume primality of points in its support. It supplies the combinatorial ingredient of the Green–Tao reduction.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §3, Theorem 3.5, equations (3.7)–(3.9). Sequential consequence: absorb the vanishing error into half the positive constant; eventual hypotheses are handled by discarding a finite initial segment.

import Definitions.Def_GreenTao_Pseudorandom

open Filter
open scoped Topology

theorem GreenTao.relative_szemeredi
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν f : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x)
    (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hdensity : ∀ᶠ n in atTop, δ ≤ GreenTao.avg (f n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ GreenTao.apAvg k (f n) := by sorry
