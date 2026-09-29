-- Prove2me | Theorems.Thm_GreenTao_prime_majorant_package
-- name    : GreenTao.prime_majorant_package
-- status  : Open
-- author  : @davidnet
-- created : 2026-09-06T01:24:53.373716+00:00
-- url     : https://prove2.me/theorems/b9cf76ec-20ec-4a7f-8e08-d718037ddc24
-- title:
--   Pseudorandom majorant and positive-density weights for W-tricked primes
-- statement:
--   For every integer $k\ge3$, there exist prime moduli $M_n\to\infty$, positive integers $W_n$, a $k$-pseudorandom family $\nu_n$ on $G_n=\mathbb Z/M_n\mathbb Z$, nonnegative real functions $f_n\le\nu_n$, and a fixed $0<\delta\le1$, such that
--
--   $$\mathbb E_{x\in G_n}f_n(x)\ge\delta\quad\text{eventually},\qquad \frac1{M_n}\mathbb E_{x\in G_n}f_n(x)^k\longrightarrow0.$$
--
--   Writing $\bar x\in\{0,\ldots,M_n-1\}$ for the natural representative, the support satisfies
--
--   $$f_n(x)>0\ \Longrightarrow\ W_n\bar x+1\text{ is prime and }2\bar x<M_n.$$
--
--   This packages the analytic majorant from Proposition 9.1 with the mean and diagonal estimates used immediately afterward in §9. The source uses a scaled modified von Mangoldt function supported in $[\epsilon_kM_n,2\epsilon_kM_n]$, where $\epsilon_k=1/(2^k(k+4)!)$; the displayed half-modulus condition is a weaker consequence for $k\ge3$. The diagonal estimate follows from the logarithmic pointwise bound recorded in that proof. The finite initial segment can be discarded when choosing the sequence of moduli. This lemma supplies prime-supported weights; it makes no assertion about the existence of arithmetic progressions.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §9, Proposition 9.1 and the proof of Theorem 1.1 assuming Proposition 9.1 (the displayed mean estimate and the following zero-difference estimate). Pseudorandomness is established in Lemma 9.7 and Propositions 9.8, 9.10; support comes from the W-tricked prime weight defined at the start of §9.

import Definitions.Def_GreenTao_Pseudorandom

open Filter
open scoped Topology

theorem GreenTao.prime_majorant_package (k : ℕ) (hk : 3 ≤ k) :
    ∃ (M : ℕ → ℕ+) (W : ℕ → ℕ) (ν f : GreenTao.Family M) (δ : ℝ),
      (∀ n, Nat.Prime (M n : ℕ)) ∧
      Tendsto (fun n => (M n : ℕ)) atTop atTop ∧
      (∀ n, 0 < W n) ∧
      GreenTao.Pseudorandom k M ν ∧
      (∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x) ∧
      0 < δ ∧ δ ≤ 1 ∧
      (∀ᶠ n in atTop, δ ≤ GreenTao.avg (f n)) ∧
      Tendsto (fun n => GreenTao.diagonalAvg k (f n)) atTop (𝓝 0) ∧
      (∀ n x, 0 < f n x →
        Nat.Prime (W n * x.val + 1) ∧ 2 * x.val < (M n : ℕ)) := by sorry
