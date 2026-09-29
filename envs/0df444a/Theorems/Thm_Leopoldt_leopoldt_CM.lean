-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_CM
-- name    : Leopoldt.leopoldt_CM
-- status  : Open
-- author  : @kbuzzard
-- created : 2026-09-09T09:32:17.299822+00:00
-- url     : https://prove2.me/theorems/2dd40267-fa5b-4b77-961a-e68942a6103f
-- title:
--   Leopoldt's conjecture holds in CM fields for odd $p$
-- statement:
--   This is Theorem 1 of the source, the conjecture it sets out to prove.
--
--   Let $p$ be an odd prime and let $\mathbb{K}$ be a CM number field, that is a totally complex quadratic extension of its maximal real subfield $\mathbb{K}^+$. Write $E = \mathcal{O}(\mathbb{K})^\times$ for the units, $U = \prod_{\wp \mid p} \mathcal{O}_\wp^\times$ for the semilocal units at $p$, $\iota : E \to U$ for the diagonal embedding, and
--   $$\bar{E} \;=\; \bigcap_{n>0} \iota(E)\cdot U^{p^n}$$
--   for the $p$-adic closure of the global units. The **Leopoldt defect** is
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; \mathbb{Z}\text{-rk}(E) \;-\; \mathbb{Z}_p\text{-rk}(\bar{E}).$$
--   The assertion is that it vanishes:
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; 0 .$$
--
--   Equivalently, the $\mathbb{Z}_p$-rank of the $p$-adic closure of the units attains Dirichlet's $\mathbb{Z}$-rank $r_1 + r_2 - 1$: units that are independent over $\mathbb{Z}$ remain independent after the diagonal embedding into the completions at the primes above $p$. For CM fields this is equivalent to the non-vanishing of the $p$-adic regulator of $\mathbb{K}$.
--
--   Leopoldt's conjecture is known for abelian extensions of $\mathbb{Q}$ by Brumer's 1967 theorem, and open in general; the CM case stated here is claimed by the source, an unrefereed preprint. By Iwasawa's theorem the defect measures the excess $\mathbb{Z}_p$-rank of the Galois group of the maximal $p$-abelian $p$-ramified extension, $\mathrm{Gal}(\Omega(\mathbb{K})/\mathbb{K}) \cong \mathbb{Z}_p^{\,r_2+1+\mathcal{D}_L(\mathbb{K})}$, so vanishing of the defect pins that rank down exactly and, for the underlying totally real field, rules out non-cyclotomic $\mathbb{Z}_p$-extensions.
--
--   **Formalization Note** Oddness of $p$ is stated as $p$ being an odd natural number alongside the primality assumption. The defect subtracts in $\mathbb{N}$ and so truncates, but since the $\mathbb{Z}_p$-rank never exceeds the $\mathbb{Z}$-rank the truncation is never triggered, and the conclusion is equivalent to equality of the two ranks. The statement has no content when Dirichlet's rank is $0$, that is for imaginary quadratic $\mathbb{K}$, and genuine content for every other CM field.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1 (Introduction), Theorem 1 (LaTeX label 'main'), p. 2, stated verbatim as: 'For odd primes p, the Leopoldt Conjecture holds in arbitrary CM extensions K/Q.' The definition of the Leopoldt Conjecture used is that of Section 1.1, p. 3: the Leopoldt defect D_L(K) = Z-rk(E) - Z_p-rk(Ebar) vanishes.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldt_CM (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    LeopoldtConjecture p K := by sorry
end Leopoldt
