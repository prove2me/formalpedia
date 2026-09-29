-- Prove2me | Theorems.Thm_MilnorConjecture_norm_residue_ker_le
-- name    : MilnorConjecture.norm_residue_ker_le
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T12:04:50.206367+00:00
-- url     : https://prove2.me/theorems/0136c27d-9846-4810-b080-e0d385e049e1
-- title:
--   Kernel of the norm residue map is $2K^M_n(F)$
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure and $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character ($\chi_a(\sigma)=0$ iff $\sigma$ fixes a chosen square root of $a$). For $a=(a_1,\dots,a_n)\in(F^\times)^n$, the Galois symbol $\mathrm{gs}(a_1,\dots,a_n)\in H^n(F,\mathbb{Z}/2)$ is the cup product $\chi_{a_1}\cup\cdots\cup\chi_{a_n}$ in continuous Galois cohomology (with $\mathrm{gs}()=1\in H^0$). Let $K^M_n(F)$ be the $n$-th Milnor K-group, with symbols $\{a_1,\dots,a_n\}$.
--
--   Let $\varphi:K^M_n(F)\to H^n(F,\mathbb{Z}/2)$ be a group homomorphism with $\varphi\{a_1,\dots,a_n\}=\mathrm{gs}(a_1,\dots,a_n)$ for all $a_i\in F^\times$ (i.e. $\varphi$ is the norm residue homomorphism). Then
--
--   $$\ker\varphi\subseteq 2\,K^M_n(F),$$
--
--   i.e. if $\varphi(x)=0$ then $x=2y$ for some $y\in K^M_n(F)$.
--
--   This is the injectivity half of the Milnor conjecture (Voevodsky): the induced map $K^M_n(F)/2\to H^n(F,\mathbb{Z}/2)$ is injective.
--
--   **Formalization Note** Since symbols generate $K^M_n(F)$, the hypothesis determines $\varphi$ uniquely; it is stated as a hypothesis so the statement does not presuppose the construction of $\varphi$.
-- source:
--   V. Voevodsky, Motivic cohomology with Z/2-coefficients, Publ. Math. IHES 98 (2003), 59-104, https://doi.org/10.1007/s10240-003-0010-6, Section 7, Corollary 7.5 (the norm residue homomorphisms K^M_n(k)/2 -> H^n_et(k, Z/2) are isomorphisms for char k != 2)

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem norm_residue_ker_le (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ)
    (φ : MilnorK F n →+ H F n) (hφ : ∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a)
    (x : MilnorK F n) (hx : φ x = 0) : ∃ y : MilnorK F n, x = 2 • y := by sorry
end MilnorConjecture
