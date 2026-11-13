-- Prove2me | Theorems.Thm_KnodelPrimeCordial_lemma_2_2
-- name    : KnodelPrimeCordial.lemma_2_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T05:59:15.589193+00:00
-- url     : https://prove2.me/theorems/8c514a8e-e18d-47ad-a9fe-b6406060b622
-- title:
--   Lemma 2.2 — coprimality of $x,y$ via the prime factors of $|x-y|$
-- statement:
--   Let $x,y$ be positive integers and let $|x-y|=p_1^{\alpha_1}p_2^{\alpha_2}\cdots p_t^{\alpha_t}$ be the prime factorization of $|x-y|$, with $p_1,\dots,p_t$ distinct primes. Then
--
--   $$
--   \gcd(x,y)=1\iff x\not\equiv 0 \pmod{p_i}\ \text{ for all } 1\le i\le t .
--   $$
--
--   When $|x-y|=1$ (so $t=0$) the right-hand side is empty and $x,y$ are coprime. The paper uses this criterion to label edges $v_iv_{i+1}$ and $v_iv_{i+5}$ whose end labels differ by $3$ or $9$.
--
--   **Formalization Note** The primes $p_1,\dots,p_t$ are `Nat.primeFactors |x − y|`, with $|x-y|$ computed in $\mathbb Z$; "$x\not\equiv 0\pmod{p}$" is `x % p ≠ 0`.
--
--   Differences from the source:
--   - encoding: |x − y| = p1^α1 ⋯ pt^αt (a product of prime powers, hence ≥ 1) → hypothesis x ≠ y; reason: the printed factorization exists exactly when x ≠ y; without it x = y = 2 would be a counterexample
--   - encoding: the distinct primes p1, …, pt of the factorization → Nat.primeFactors (Int.natAbs (x − y)); reason: same finite set of primes
--   - encoding: x ≢ 0 mod p_i → x % p ≠ 0; reason: same condition
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.2, p.3 (PDF p.3)

import Mathlib

namespace KnodelPrimeCordial

/-- **Lemma 2.2** (Haque, Khanam, Shahriar, *Prime cordial labeling of Knödel graph*,
manuscript (2026), §2, p.3): "Let x, y be two positive integers, and let |x − y| =
p1^α1 p2^α2 . . . pt^αt, where pi are distinct prime factors and αi are their orders. Then they
are coprime iff x ≢ 0 mod pi for 1 ≤ i ≤ t."

For positive integers `x ≠ y`, `x` and `y` are coprime iff `x mod p ≠ 0` for every prime `p`
dividing `|x − y|`.

**Formalization Note** The primes `p₁, …, p_t` of the factorization of `|x − y|` are
`Nat.primeFactors |x − y|`, with `|x − y|` computed in `ℤ`. The hypothesis `x ≠ y` encodes the
printed factorization hypothesis: `|x − y|` is a (possibly empty) product of prime powers,
hence at least `1`. -/
theorem lemma_2_2 (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    Nat.Coprime x y ↔ ∀ p ∈ (Int.natAbs ((x : ℤ) - (y : ℤ))).primeFactors, x % p ≠ 0 := by sorry

end KnodelPrimeCordial
