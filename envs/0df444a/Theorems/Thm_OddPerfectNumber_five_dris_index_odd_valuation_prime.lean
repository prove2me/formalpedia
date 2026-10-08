-- Prove2me | Theorems.Thm_OddPerfectNumber_five_dris_index_odd_valuation_prime
-- name    : OddPerfectNumber.five_dris_index_odd_valuation_prime
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-05T18:19:47.329497+00:00
-- url     : https://prove2.me/theorems/5f52246d-6442-46a2-800b-66b200a32c17
-- title:
--   Dris index at $k=5$: some prime $\ell\ne 3$ dividing $p^4+p^2+1$ divides $s$ to an odd power
-- statement:
--   Let $p$ be an odd prime and let $m,s$ be natural numbers with $s>0$ such that the first Dris relation at exponent $k=5$,
--   $$2m^{2}=\sigma(p^{5})\,s,$$
--   holds. Then there is a prime $\ell\neq 3$ with
--   $$\ell \mid p^{4}+p^{2}+1 \qquad\text{and}\qquad v_\ell(s)\ \text{odd}.$$
--
--   In particular the Dris index $s$ is never a power of $3$, and it is never coprime to $p^4+p^2+1$ away from the prime $3$. Only the first relation is used, not $\sigma(m^2)=p^5 s$.
--
--   **Idea.** Write $\sigma(p^5)=(p+1)(p^2+p+1)(p^2-p+1)=2ABC$ with $A=(p+1)/2$, $B=p^2+p+1$, $C=p^2-p+1$. Then $m^2=ABC\,s$. The numbers $B,C$ are pairwise coprime, $B$ is coprime to $A$, and $\gcd(C,A)\mid 3$; moreover $B$ lies strictly between $p^2$ and $(p+1)^2$ and $C$ strictly between $(p-1)^2$ and $p^2$, so neither is a square. As $3$ divides at most one of $B,C$, one of them, $X$, is prime to $3$; it is coprime to the other factors of $ABC$, so any prime $\ell\mid X$ has $v_\ell(m^2)=v_\ell(X)+v_\ell(s)$. Since $X$ is not a square it has a prime $\ell$ with $v_\ell(X)$ odd, and then $v_\ell(s)$ is odd.
--
--   **Formalization Note** The statement is an elementary lemma proved for this mission; it is not taken from the literature. The hypothesis $s>0$ only excludes the degenerate solution $m=s=0$.
-- source:
--   https://prove2.me/missions/f37bda44-314b-4d8e-8917-fe26209e0c9c

import Mathlib

namespace OddPerfectNumber

theorem five_dris_index_odd_valuation_prime (p m s : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : 0 < s) (heq : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s) :
    ∃ ℓ : Nat, ℓ.Prime ∧ ℓ ≠ 3 ∧ ℓ ∣ p ^ 4 + p ^ 2 + 1 ∧ Odd (padicValNat ℓ s) := by sorry

end OddPerfectNumber
