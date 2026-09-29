-- Prove2me | Theorems.Thm_MilnorConjecture_norm_residue_ker_le_two
-- name    : MilnorConjecture.norm_residue_ker_le_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T12:26:17.027787+00:00
-- url     : https://prove2.me/theorems/0a4c33cd-d1ff-4afe-b83e-f80998b3e9e5
-- title:
--   Merkurjev's theorem: kernel of the norm residue map $K^M_2(F)\to H^2(F,\mathbb{Z}/2)$ is $2K^M_2(F)$
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure, $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$ with its Krull topology, and $H^n(F,\mathbb{Z}/2)$ the continuous cohomology of $G_F$ with coefficients in the trivial module $\mathbb{Z}/2$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character, and for $a=(a_1,\dots,a_n)\in(F^\times)^n$ let $\mathrm{gs}(a_1,\dots,a_n)=\chi_{a_1}\cup\cdots\cup\chi_{a_n}\in H^n(F,\mathbb{Z}/2)$ be the Galois symbol. Let $K^M_n(F)$ be the $n$-th Milnor K-group with symbols $\{a_1,\dots,a_n\}$.
--
--   Let $\varphi:K^M_2(F)\to H^2(F,\mathbb{Z}/2)$ be a group homomorphism with $\varphi\{a,b\}=\mathrm{gs}(a,b)=\chi_a\cup\chi_b$ for all $a,b\in F^\times$ (the degree-$2$ norm residue homomorphism). Then
--
--   $$\ker\varphi\subseteq 2\,K^M_2(F),$$
--
--   i.e. if $\varphi(x)=0$ then $x=2y$ for some $y\in K^M_2(F)$.
--
--   This is the injectivity half of Merkurjev's theorem $K_2(F)/2\cong H^2(F,\mathbb{Z}/2)\cong {}_2\mathrm{Br}(F)$, the degree-$2$ case of the Milnor conjecture. It is the case $n=2$ of `MilnorConjecture.norm_residue_ker_le_of_two_le`.
--
--   **Formalization note.** As in `norm_residue_ker_le_of_two_le`, $\varphi$ is a hypothesis; it is determined by its values on symbols.
-- source:
--   A. S. Merkurjev, On the norm residue symbol of degree 2, Dokl. Akad. Nauk SSSR 261 (1981), 542-547 (Soviet Math. Dokl. 24 (1981), 546-551), main theorem (injectivity of K_2(F)/2 -> Br_2(F)); also V. Voevodsky, Motivic cohomology with Z/2-coefficients, Publ. Math. IHES 98 (2003), Corollary 7.5 (p. 97), case n = 2.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem norm_residue_ker_le_two (F : Type) [Field F] [NeZero (2 : F)]
    (φ : MilnorK F 2 →+ H F 2) (hφ : ∀ a : Fin 2 → Fˣ, φ (symbol a) = galoisSymbol a)
    (x : MilnorK F 2) (hx : φ x = 0) : ∃ y : MilnorK F 2, x = 2 • y := by sorry
end MilnorConjecture
