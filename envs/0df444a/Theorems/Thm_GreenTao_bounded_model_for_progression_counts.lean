-- Prove2me | Theorems.Thm_GreenTao_bounded_model_for_progression_counts
-- name    : GreenTao.bounded_model_for_progression_counts
-- status  : Open
-- author  : @davidnet
-- created : 2026-09-06T02:15:23.296613+00:00
-- url     : https://prove2.me/theorems/934d643f-c570-474a-abb4-5fe5683e9756
-- title:
--   Bounded model preserving mean and a lower progression count
-- statement:
--   Let $k\ge3$, let $M_n$ be prime moduli tending to infinity, and let $\nu_n$ be a $k$-pseudorandom family in the sense of Green–Tao Definitions 3.1–3.3. Suppose that real functions $f_n$ satisfy $0\le f_n\le\nu_n$ pointwise. For every fixed $\eta>0$, all sufficiently large $n$ admit a function $g_n:\mathbb Z/M_n\mathbb Z\to[0,1]$ such that
--
--   $$\mathbb E g_n\ge\mathbb E f_n-\eta,\qquad T_k(f_n)\ge T_k(g_n)-\eta,$$
--
--   where
--
--   $$T_k(h)=\mathbb E_{x,r}\prod_{j=0}^{k-1}h(x+jr).$$
--
--   The model may depend on $n$ and $\eta$. No lower density hypothesis is imposed, and the progression-count comparison is one-sided. This is the bounded-model consequence of the structure and generalized von Neumann results used in §8. It separates the approximation step for functions dominated by pseudorandom measures from Szemerédi's theorem for bounded functions.
--
--   **Formalization Note.** The range bound is exactly $[0,1]$. The small normalization adjustment described in footnote 16 is included in the prescribed error $\eta$.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §8, Proposition 8.1, equations (8.1)–(8.3), and the mean and mixed-progression estimates in the proof of Theorem 3.5 assuming Proposition 8.1; §5 Proposition 5.3; §8 footnote 16 for normalization to [0,1].

import Definitions.Def_GreenTao_Pseudorandom

open Filter

theorem GreenTao.bounded_model_for_progression_counts
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν f : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∃ g : ZMod (M n : ℕ) → ℝ,
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      GreenTao.avg (f n) - η ≤ GreenTao.avg g ∧
      GreenTao.apAvg k g - η ≤ GreenTao.apAvg k (f n) := by sorry
