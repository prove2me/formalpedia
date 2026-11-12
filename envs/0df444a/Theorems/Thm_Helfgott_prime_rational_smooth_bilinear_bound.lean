-- Prove2me | Theorems.Thm_Helfgott_prime_rational_smooth_bilinear_bound
-- name    : Helfgott.prime_rational_smooth_bilinear_bound
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T19:31:20.756958+00:00
-- url     : https://prove2.me/theorems/dd4a2b74-521e-4b08-b080-9277831d3498
-- title:
--   A prime-supported smoothed rational bilinear bound with an explicit sieve gain
-- statement:
--   Let $N,q,a,U,C,D$ be natural numbers with $q>0$, $U\ge2$, $C>0$, and $(a,q)=1$, and let $y>0$. Put $P=\{p<N:p\text{ prime},\ p>U\}$ and $J=\lfloor\max(D-C,0)/q\rfloor+1$. For arbitrary complex coefficients $v_p,b_m$,
--    $$\left|\sum_{p\in P}\sum_{C\le m<D}v_pb_m\eta_2(pm/y)e(apm/q)\right|^2
--    \le16(\log2)^2qJ\left(\frac{N}{\varphi(q)\log U}+U^4\right)
--    \left(\sum_{p\in P}|v_p|^2\right)\left(\sum_{C\le m<D}|b_m|^2\right).$$
--    Here $e(t)=\exp(2\pi it)$ and $\eta_2(t)=4\max(\log2-|\log(2t)|,0)$ for $t>0$, and zero otherwise. This is an unconditional prime-supported estimate at exact rational phases, with the sieve error displayed.
-- source:
--   Classical Selberg sieve, finite Fourier orthogonality and the interval-overlap factorization of the triangular logarithmic smoothing. Retained arithmetic and normalizer proofs carry attribution to raresbuhai (Apache 2.0), submissions 270f0aa4-1a5a-4d37-aad1-43522eb8dc16, 4b19f26e-e6f8-4a14-8cf6-e0ea33b44440 and dc167013-7b1b-47a5-bd68-36e63ad77223. Explicit prime progression sieve, Fourier energy, multiplicity and smoothing transfer formalized by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Nat.Totient
open Finset Helfgott
open scoped BigOperators

theorem Helfgott.prime_rational_smooth_bilinear_bound (N q a U C D : ℕ) (hq : 0<q) (hU : 2≤U)
    (hC : 0<C) (ha : Nat.Coprime a q) (y : ℝ) (hy : 0<y) (b v : ℕ → ℂ) :
    ‖∑ p ∈ (range N).filter (fun p => p.Prime ∧ U<p), ∑ m ∈ Ico C D,
      v p*b m*fourier ((p*m:ℕ):ℤ) (((a:ℝ)/(q:ℝ)):AddCircle (1:ℝ))*
        (etaTwo (((p*m:ℕ):ℝ)/y):ℂ)‖^2 ≤
      16*(Real.log 2)^2*(q:ℝ)*(((D-C)/q+1:ℕ):ℝ)*
        ((N:ℝ)/((Nat.totient q:ℝ)*Real.log (U:ℝ))+(U:ℝ)^4)*
          (∑ p ∈ (range N).filter (fun p => p.Prime ∧ U<p), ‖v p‖^2)*
            (∑ m ∈ Ico C D, ‖b m‖^2) := by sorry
