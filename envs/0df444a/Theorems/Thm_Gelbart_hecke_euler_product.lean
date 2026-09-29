-- Prove2me | Theorems.Thm_Gelbart_hecke_euler_product
-- name    : Gelbart.hecke_euler_product
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:45:57.465676+00:00
-- url     : https://prove2.me/theorems/5320d71f-4d83-4df4-9a14-ec1b7592ecdf
-- title:
--   Theorem 2 (Hecke): multiplicativity gives an Euler product
-- statement:
--   The Euler-product half of Hecke's Theorem 2 (p. 188–189, display (2)). If $a_n = O(n^{c})$ with $c > 0$, $a_1 = 1$, and the coefficients are multiplicative ($a_{mn} = a_m a_n$ whenever $\gcd(m,n) = 1$), then for $\operatorname{Re} s > c+1$ $$\varphi(s) = \sum_{n \ge 1}\frac{a_n}{n^{s}} = \prod_{p}\left(\sum_{m \ge 0}\frac{a_{p^{m}}}{p^{ms}}\right),$$ the product over primes being understood as the limit of its partial products over the primes below $N$. Gelbart states this as the "formal computation" that $\varphi$ factors whenever the $a_n$ are multiplicative; the theorem here supplies the convergence.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, pp. 188-189, §II.B.2, display (2) and Theorem 2 (Hecke)

import Definitions.Def_Gelbart_hecke_series

namespace Gelbart

theorem hecke_euler_product
    (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : HeckeCoeffGrowth a c)
    (h1 : a 1 = 1) (hmul : ∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n)
    {s : ℂ} (hs : c + 1 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∏ p ∈ (Finset.range N).filter Nat.Prime,
        ∑' m : ℕ, a (p ^ m) / (p : ℂ) ^ ((m : ℂ) * s))
      Filter.atTop (nhds (LSeries a s)) := by sorry

end Gelbart
