-- Prove2me | Theorems.Thm_IwasawaMainConjecture_herbrand_ribet
-- name    : IwasawaMainConjecture.herbrand_ribet
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T17:25:31.706111+00:00
-- url     : https://prove2.me/theorems/8c5e92d5-5504-4560-8678-86fe33cbc71a
-- title:
--   Herbrand–Ribet theorem
-- statement:
--   Let $p$ be a prime and let $A_0$ be the $p$-part of the ideal class group of $\mathbb{Q}(\zeta_p)$, viewed as a $\mathbb{Z}_p$-module with its Galois action. Let $i$ be an odd integer with $3 \le i \le p-2$. Then the $\omega^i$-eigenspace
--   $$A_0^{(\omega^i)} = \{x \in A_0 : \sigma x = \omega(\sigma)^i x \text{ for all } \sigma \in \Delta\}$$
--   is nonzero if and only if
--   $$p \mid B_{p-i},$$
--   where $B_{p-i}$ is the Bernoulli number (more precisely, $p$ divides its numerator).
--
--   Herbrand (1932) proved "only if" and Ribet (1976) proved "if". The source lists the theorem as a consequence of the main conjecture. Ribet's method is also the model for the Mazur–Wiles proof.
--
--   **Formalization Note** $\Delta$ is described inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ as the set of $\sigma$ whose cyclotomic character $c$ satisfies $c^{p-1}=1$, and then $\omega(\sigma) = c$. For $p \le 3$ there is no such $i$ and the statement is vacuous.
-- source:
--   Wikipedia, "Main conjecture of Iwasawa theory", revision oldid=1367440598, https://en.wikipedia.org/w/index.php?title=Main_conjecture_of_Iwasawa_theory&oldid=1367440598, lead section ("The Herbrand–Ribet theorem and the Gras conjecture are both easy consequences of the main conjecture"); Washington, Introduction to Cyclotomic Fields, 2nd ed. (1997), Thm 6.17 and §15

import Definitions.Def_IwasawaMainConjecture_algebraic
import Definitions.Def_IwasawaMainConjecture_analytic

open scoped Polynomial

namespace IwasawaMainConjecture
theorem herbrand_ribet (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : Odd i) (h3 : 3 ≤ i)
    (hip : i ≤ p - 2) :
    (∃ x : Additive (A p 0), x ≠ 0 ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℤ_[p]),
        IsCyclotomicCharValue p σ c → c ^ (p - 1) = 1 →
          (galA p σ 0).toAdditive x = c ^ i • x) ↔
      (p : ℤ) ∣ (bernoulli (p - i)).num := by sorry
end IwasawaMainConjecture
