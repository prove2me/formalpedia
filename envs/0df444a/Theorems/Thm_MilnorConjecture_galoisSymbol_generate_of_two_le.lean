-- Prove2me | Theorems.Thm_MilnorConjecture_galoisSymbol_generate_of_two_le
-- name    : MilnorConjecture.galoisSymbol_generate_of_two_le
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T03:44:48.883025+00:00
-- url     : https://prove2.me/theorems/50f5541a-aba7-479f-844d-f4d2a7a6a2f4
-- title:
--   Galois symbols generate $H^n(F,\mathbb{Z}/2)$ for $n\ge 2$
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure and $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$ with its Krull topology, and let $H^n(F,\mathbb{Z}/2)$ be the continuous cohomology of $G_F$ with coefficients in the trivial module $\mathbb{Z}/2$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character ($\chi_a(\sigma)=0$ iff $\sigma$ fixes a chosen square root of $a$). For $a=(a_1,\dots,a_n)\in(F^\times)^n$, the Galois symbol $\mathrm{gs}(a_1,\dots,a_n)\in H^n(F,\mathbb{Z}/2)$ is the cup product $\chi_{a_1}\cup\cdots\cup\chi_{a_n}$ (with $\mathrm{gs}()=1\in H^0$).
--
--   Then for every $n\ge 2$ the Galois symbols generate the cohomology group:
--
--   $$\big\langle\, \mathrm{gs}(a_1,\dots,a_n) \;:\; a_1,\dots,a_n\in F^\times \,\big\rangle \;=\; H^n(F,\mathbb{Z}/2)\qquad (n\ge 2).$$
--
--   This is the surjectivity half of the Milnor conjecture in degrees $\ge 2$ (Merkurjev for $n=2$, Voevodsky in general); the cases $n\le 1$ are classical.
-- source:
--   V. Voevodsky, Motivic cohomology with Z/2-coefficients, Publ. Math. IHES 98 (2003), 59-104, https://doi.org/10.1007/s10240-003-0010-6, Section 7, Corollary 7.5 (p. 97) in degrees n >= 2; obtained there from Corollary 6.10 (p. 91) and Theorem 7.4.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem galoisSymbol_generate_of_two_le (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) (hn : 2 ≤ n) :
    AddSubgroup.closure (Set.range (galoisSymbol (F := F) (n := n))) = ⊤ := by sorry
end MilnorConjecture
