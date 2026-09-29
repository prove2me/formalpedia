-- Prove2me | Theorems.Thm_GreenTao_prime_weight_fixed_modulus_mean
-- name    : GreenTao.prime_weight_fixed_modulus_mean
-- status  : Open
-- author  : @davidnet
-- created : 2026-09-06T02:30:21.078773+00:00
-- url     : https://prove2.me/theorems/e694b015-8489-490a-a533-520747240869
-- title:
--   Mean of the W-tricked prime weight for a fixed modulus
-- statement:
--   Fix an integer $k\ge3$ and an integer $W>0$. Let $M_n$ be any sequence of positive integers tending to infinity. With $F_{k,W,M_n}$ denoting the scaled prime-only weight supported on $[\epsilon_k M_n,2\epsilon_k M_n]$, one has
--
--   $$\lim_{n\to\infty}\frac1{M_n}\sum_{x\in\mathbb Z/M_n\mathbb Z}F_{k,W,M_n}(x)=a_k\epsilon_k,$$
--
--   where $a_k=1/(k2^{k+5})$ and $\epsilon_k=1/(2^k(k+4)!)$.
--
--   The modulus $W$ is fixed independently of $n$; no uniform rate in $W$ is asserted, and the integers $M_n$ need not be prime. This is the fixed-modulus prime number theorem in the residue class $1\pmod W$, expressed using the short-interval prime weight. It provides the density input independently of the pseudorandom sieve estimate.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §9, the prime-distribution statement and footnote 21 preceding Proposition 9.1, and the displayed mean formula in the proof of Theorem 1.1 assuming Proposition 9.1; specialized to fixed W and arbitrary positive moduli tending to infinity.

import Definitions.Def_GreenTao_PrimeWeight

open Filter
open scoped Topology

theorem GreenTao.prime_weight_fixed_modulus_mean
    (k : ℕ) (hk : 3 ≤ k) (W : ℕ) (hW : 0 < W)
    (M : ℕ → ℕ+) (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) :
    Tendsto (fun n => GreenTao.avg (GreenTao.primeWeight k W (m := M n)))
      atTop (𝓝 (GreenTao.primeScale k * GreenTao.primeInterval k)) := by sorry
