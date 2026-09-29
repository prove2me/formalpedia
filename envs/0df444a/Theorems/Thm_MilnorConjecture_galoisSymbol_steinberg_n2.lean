-- Prove2me | Theorems.Thm_MilnorConjecture_galoisSymbol_steinberg_n2
-- name    : MilnorConjecture.galoisSymbol_steinberg_n2
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-26T05:49:45.270988+00:00
-- url     : https://prove2.me/theorems/f09453d2-d84d-4b4b-a1ed-4a9cf2e41778
-- title:
--   Steinberg relation for the Galois symbol in degree two
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure and $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character. For $a=(a_1,a_2)\in(F^\times)^2$, the degree-2 Galois symbol $\mathrm{gs}(a_1,a_2)=\chi_{a_1}\cup\chi_{a_2}\in H^2(F,\mathbb{Z}/2)$ is the cup product of the two Kummer characters in continuous Galois cohomology.
--
--   Then Tate's relation holds: if $a_1+a_2=1$ in $F$, then $\mathrm{gs}(a_1,a_2)=0$. This is the $n=2$ case of the Steinberg relation; the general-$n$ Steinberg relation (MilnorConjecture.galoisSymbol_steinberg) follows from it by associativity of the cup product, using the cup-factorization lemmas in the platform bundle (prodCochain_succ, fcob_mul_tail, fcob_prodCochain). The standard proof is the quaternion norm criterion (Matsumoto's theorem): $1-a = N_{F(\sqrt{a})/F}(1-\sqrt{a})$ forces the quaternion algebra $(a,1-a)$ to split, so its class vanishes in $\mathrm{Br}(F)[2]\cong H^2(F,\mathbb{Z}/2)$.
--
--   Decomposition node for MilnorConjecture.galoisSymbol_steinberg: the general-$n$ statement is an elementary assembly over this $n=2$ core, which is the genuine deep input (well-definedness of the norm residue map, Matsumoto direction).
-- source:
--   J. Milnor, Algebraic K-theory and quadratic forms, Invent. Math. 9 (1970), 318-344, https://doi.org/10.1007/BF01425486, Section 6 (definition of the homomorphism h_n : K_n F / 2 K_n F -> H^n(F, Z/2), degree-2 case). Decomposition of MilnorConjecture.galoisSymbol_steinberg: the n=2 vanishing (Tate's relation) is the deep input; the general-n case reduces to it by cup-factorization.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem galoisSymbol_steinberg_n2 (F : Type) [Field F] [NeZero (2 : F)]
    (a : Fin 2 → Fˣ) (h : (a 0 : F) + (a 1 : F) = 1) :
    galoisSymbol a = 0 := by sorry
end MilnorConjecture
