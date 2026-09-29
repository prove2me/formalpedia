-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_totallyReal
-- name    : Leopoldt.leopoldt_totallyReal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-09T14:45:16.766223+00:00
-- url     : https://prove2.me/theorems/9261a497-a37c-4687-ba0c-f54a8e8b553c
-- title:
--   Leopoldt's conjecture for totally real fields
-- statement:
--   Let $p$ be an odd prime and let $\mathbb{F}$ be a totally real number field, that is, a number field all of whose infinite places are real. Then the Leopoldt defect of $\mathbb{F}$ at $p$ vanishes:
--
--   $$\mathcal{D}_L(\mathbb{F}) \;=\; 0 .$$
--
--   This is Leopoldt's conjecture for totally real fields. By Iwasawa's theorem $\mathrm{Gal}(\Omega(\mathbb{F})/\mathbb{F}) \cong \mathbb{Z}_p^{\,r_2+1+\mathcal{D}_L(\mathbb{F})}$ with $r_2 = 0$ here, so the assertion is equivalent to the statement the source records as Conjecture 1: the only $\mathbb{Z}_p$-extension of a totally real field is the cyclotomic one. It is exactly the assumption whose negation the source's proof of Theorem 1 sets out to contradict.
--
--   For a totally real field Dirichlet's rank is $r = [\mathbb{F}:\mathbb{Q}] - 1$, and the conjecture says that a system of $r$ independent units stays independent after the diagonal embedding into the units of the completions at the primes above $p$ - equivalently, that the $p$-adic regulator of $\mathbb{F}$ does not vanish. The case $\mathbb{F}/\mathbb{Q}$ abelian is Brumer's theorem; beyond it the statement is open, and it is the substantive half of the CM case: together with the descent of a positive defect from a CM field to its maximal real subfield it gives Theorem 1 of the source.
--
--   **Formalization note.** `IsTotallyReal F` is Mathlib's predicate that every infinite place of $\mathbb{F}$ is real. Oddness of $p$ is the standing assumption of Section 1.1 of the source and of its Theorem 1; the conjecture itself is expected for every prime.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1.1 (Notations and fundamental facts), p. 4, Conjecture 1, stated there verbatim as: "Conjecture 1 ( Leopoldt ). The only Z_p-extension of a totally real field is the cyclotomic one, and a CM number field has no CM Z_p-extensions except for the cyclotomic one.", introduced on the same page as "an equivalent formulation of the Leopoldt conjecture" for these fields; the defect form used here is the definition given on p. 3, D_L(K) = Z-rk(E) - Z_p-rk(Ebar). Original conjecture: H. Leopoldt, Zur Arithmetik in Abelschen Zahlkoerpern, J. reine angew. Math. 209 (1962), 54-71, https://doi.org/10.1515/crll.1962.209.54.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldt_totallyReal (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F] :
    LeopoldtConjecture p F := by sorry
end Leopoldt
