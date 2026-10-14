-- Prove2me | Theorems.Thm_IwasawaMainConjecture_iwasawa_power_series_existsUnique
-- name    : IwasawaMainConjecture.iwasawa_power_series_existsUnique
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T17:23:10.976715+00:00
-- url     : https://prove2.me/theorems/2d8f173b-c0ea-43e1-91d5-c3310c93dc58
-- title:
--   Existence and uniqueness of the Iwasawa power series $G_p(\omega^j,T)$
-- statement:
--   Let $p$ be a prime, let $j$ be an even integer with $j \not\equiv 0 \pmod{p-1}$, and let $u \in \mathbb{Z}_p^\times$ be a topological generator of $1 + p\mathbb{Z}_p$. Then there is exactly one power series $G = \sum_n a_n T^n \in \mathbb{Z}_p[[T]]$ such that for every integer $k \ge 1$
--   $$G(u^{1-k} - 1) = \sum_{n\ge 0} a_n (u^{1-k}-1)^n = -\frac{B_{k,\omega^{j-k}}}{k},$$
--   where $B_{k,\chi} = p^{k-1}\sum_{a=1}^{p}\chi(a)B_k(a/p)$ is the generalized Bernoulli number of the character $\chi$ modulo $p$ and $\omega$ is the Teichmüller character.
--
--   In the source's notation, this is the statement that the Kubota–Leopoldt $p$-adic $L$-function $L_p(\omega^j, s)$, characterised by $L_p(\omega^j, 1-k) = -B_k(\omega^{j-k})/k$, is given by a power series with $\mathbb{Z}_p$-coefficients: $G_p(\omega^j, u^s - 1) = L_p(\omega^j, s)$. This makes $G_p(\omega^{1-i}, T)$ in the main conjecture well defined.
--
--   **Formalization Note** For $p = 2$ or $p = 3$ the hypotheses cannot be met (every even $j$ is divisible by $p-1$), so the statement is vacuous there.
-- source:
--   Wikipedia, "Main conjecture of Iwasawa theory", revision oldid=1367440598, https://en.wikipedia.org/w/index.php?title=Main_conjecture_of_Iwasawa_theory&oldid=1367440598, section "Statement" (definitions of L_p and G_p); Iwasawa, On p-adic L-functions, Ann. of Math. 89 (1969), https://doi.org/10.2307/1970817

import Definitions.Def_IwasawaMainConjecture_algebraic
import Definitions.Def_IwasawaMainConjecture_analytic

open scoped Polynomial

namespace IwasawaMainConjecture
theorem iwasawa_power_series_existsUnique (p : ℕ) [Fact p.Prime] (j : ℤ) (hj : Even j)
    (hj0 : ¬ ((p : ℤ) - 1) ∣ j) (u : ℤ_[p]ˣ) (hu : IsTopologicalGenerator p u) :
    ∃! G : PowerSeries ℤ_[p], IsIwasawaPowerSeries p u j G := by sorry
end IwasawaMainConjecture
