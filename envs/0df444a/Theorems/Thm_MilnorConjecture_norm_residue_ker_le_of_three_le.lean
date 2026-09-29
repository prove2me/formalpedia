-- Prove2me | Theorems.Thm_MilnorConjecture_norm_residue_ker_le_of_three_le
-- name    : MilnorConjecture.norm_residue_ker_le_of_three_le
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T12:26:19.603317+00:00
-- url     : https://prove2.me/theorems/45c0e3c4-4b36-4939-a1ce-87e45ecfc07e
-- title:
--   Kernel of the norm residue map is $2K^M_n(F)$ for $n\ge 3$
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure, $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$ with its Krull topology, and $H^n(F,\mathbb{Z}/2)$ the continuous cohomology of $G_F$ with coefficients in the trivial module $\mathbb{Z}/2$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character, and for $a=(a_1,\dots,a_n)\in(F^\times)^n$ let $\mathrm{gs}(a_1,\dots,a_n)=\chi_{a_1}\cup\cdots\cup\chi_{a_n}\in H^n(F,\mathbb{Z}/2)$ be the Galois symbol. Let $K^M_n(F)$ be the $n$-th Milnor K-group with symbols $\{a_1,\dots,a_n\}$.
--
--   Let $n\ge 3$ and let $\varphi:K^M_n(F)\to H^n(F,\mathbb{Z}/2)$ be a group homomorphism with $\varphi\{a_1,\dots,a_n\}=\mathrm{gs}(a_1,\dots,a_n)$ for all $a_i\in F^\times$ (the norm residue homomorphism). Then
--
--   $$\ker\varphi\subseteq 2\,K^M_n(F),$$
--
--   i.e. if $\varphi(x)=0$ then $x=2y$ for some $y\in K^M_n(F)$.
--
--   This is the injectivity half of the Milnor conjecture in degrees $\ge 3$ (Merkurjev–Suslin and Rost for $n=3$, Voevodsky in general). Together with the degree-$2$ case `MilnorConjecture.norm_residue_ker_le_two` (Merkurjev) it gives `MilnorConjecture.norm_residue_ker_le_of_two_le`.
--
--   **Formalization note.** As in `norm_residue_ker_le_of_two_le`, $\varphi$ is a hypothesis; it is determined by its values on symbols.
-- source:
--   V. Voevodsky, Motivic cohomology with Z/2-coefficients, Publ. Math. IHES 98 (2003), 59-104, https://doi.org/10.1007/s10240-003-0010-6, Section 7, Corollary 7.5 (p. 97) in degrees n >= 3; obtained there from Corollary 6.10 (p. 91) and Theorem 7.4.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem norm_residue_ker_le_of_three_le (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) (hn : 3 ≤ n)
    (φ : MilnorK F n →+ H F n) (hφ : ∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a)
    (x : MilnorK F n) (hx : φ x = 0) : ∃ y : MilnorK F n, x = 2 • y := by sorry
end MilnorConjecture
