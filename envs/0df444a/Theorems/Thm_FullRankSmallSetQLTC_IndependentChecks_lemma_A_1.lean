-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_lemma_A_1
-- name    : FullRankSmallSetQLTC.IndependentChecks.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:15.08081+00:00
-- url     : https://prove2.me/theorems/6245ea6c-c1e9-4042-82ab-6be95bcf7e0d
-- title:
--   Lemma A.1 — unique factorization of the norm shells A(n)
-- statement:
--   Let $p_1,\dots,p_k$ be distinct primes with $p_i\equiv1\pmod4$, listed in any prescribed order, and put $n=p_1\cdots p_k$. Let $A(m)$ be the set of integral quaternions of norm $m$ with odd real part, modulo $\pm1$. Then
--   $$|A(n)|=\prod_{i=1}^k(p_i+1),$$
--   and multiplication induces a bijection
--   $$A(p_1)\times\cdots\times A(p_k)\xrightarrow{\ \sim\ }A(n).$$
--   In particular $|A(p)|=p+1$, and $A(p_i)A(p_j)=A(p_ip_j)=A(p_j)A(p_i)$ for $i\ne j$.
--
--   This is the unique-factorization input for the LPS generators and for the cubical generating sets of §4.2.
--
--   Differences from the source:
--   - encoding: A(n) = {a ∈ L(ℤ) : N(a) = n, a₀ odd}/{±1} → the set APos n of representatives with positive real part; a product of classes is written sgnNorm of the product of representatives; reason: the real part of each element is odd, hence nonzero, so each class has exactly one representative with a₀ > 0; same instances
--   - encoding: for every prescribed ordering of p₁,…,p_k → the primes are given as a duplicate-free list ps in that order; the clauses on |A(p)| and A(p_i)A(p_j) are stated for primes of the list; reason: every ordering of a finite set of primes is such a list, including the empty list; for k = 0, A(1) and the empty product are both singletons
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Lemma A.1, p. 29 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Quaternion Pointwise

/-- **Lemma A.1** ([HLM+25, Lemma 4.8], p. 29). Let `p₁, …, p_k` be distinct primes `≡ 1 (mod 4)`
(listed in any prescribed order) and `n = p₁ ⋯ p_k`. Then `|A(n)| = ∏ (p_i + 1)`, and
multiplication induces a bijection `A(p₁) × ⋯ × A(p_k) → A(n)` (classes modulo `±1`, written by
their representatives with positive real part). In particular `|A(p)| = p + 1`, and
`A(p_i)A(p_j) = A(p_ip_j) = A(p_j)A(p_i)` for `i ≠ j`.
The empty prime list is allowed: `A(1)` and the empty product are singletons. -/
theorem lemma_A_1 (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime ∧ p % 4 = 1) :
    (APos ps.prod).ncard = (ps.map (· + 1)).prod ∧
    Set.BijOn (fun f : Fin ps.length → ℍ[ℤ] => sgnNorm (List.ofFn f).prod)
      (Set.univ.pi fun i => APos (ps.get i)) (APos ps.prod) ∧
    (∀ p ∈ ps, (APos p).ncard = p + 1) ∧
    (∀ p ∈ ps, ∀ q ∈ ps, p ≠ q →
      (fun ab : ℍ[ℤ] × ℍ[ℤ] => sgnNorm (ab.1 * ab.2)) '' (APos p ×ˢ APos q) = APos (p * q) ∧
      (fun ab : ℍ[ℤ] × ℍ[ℤ] => sgnNorm (ab.2 * ab.1)) '' (APos p ×ˢ APos q) = APos (p * q)) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
