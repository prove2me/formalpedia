-- Prove2me | Theorems.Thm_MilnorConjecture_norm_residue_ker_le_of_two_le
-- name    : MilnorConjecture.norm_residue_ker_le_of_two_le
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T03:44:49.988749+00:00
-- url     : https://prove2.me/theorems/4a420455-5cbf-4855-85f8-0cda6b87bff2
-- title:
--   Kernel of the norm residue map is $2K^M_n(F)$ for $n\ge 2$
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure and $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$ with its Krull topology, and let $H^n(F,\mathbb{Z}/2)$ be the continuous cohomology of $G_F$ with coefficients in the trivial module $\mathbb{Z}/2$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character ($\chi_a(\sigma)=0$ iff $\sigma$ fixes a chosen square root of $a$). For $a=(a_1,\dots,a_n)\in(F^\times)^n$, the Galois symbol $\mathrm{gs}(a_1,\dots,a_n)\in H^n(F,\mathbb{Z}/2)$ is the cup product $\chi_{a_1}\cup\cdots\cup\chi_{a_n}$ (with $\mathrm{gs}()=1\in H^0$). Let $K^M_n(F)$ be the $n$-th Milnor K-group, with symbols $\{a_1,\dots,a_n\}$.
--
--   Let $n\ge 2$ and let $\varphi:K^M_n(F)\to H^n(F,\mathbb{Z}/2)$ be a group homomorphism with $\varphi\{a_1,\dots,a_n\}=\mathrm{gs}(a_1,\dots,a_n)$ for all $a_i\in F^\times$ (the norm residue homomorphism). Then
--
--   $$\ker\varphi\subseteq 2\,K^M_n(F),$$
--
--   i.e. if $\varphi(x)=0$ then $x=2y$ for some $y\in K^M_n(F)$.
--
--   This is the injectivity half of the Milnor conjecture in degrees $\ge 2$ (Merkurjev for $n=2$, Voevodsky in general); the cases $n\le 1$ are classical.
--
--   **Formalization Note** As in `norm_residue_ker_le`, $\varphi$ is a hypothesis; it is determined by the condition on symbols.
-- source:
--   V. Voevodsky, Motivic cohomology with Z/2-coefficients, Publ. Math. IHES 98 (2003), 59-104, https://doi.org/10.1007/s10240-003-0010-6, Section 7, Corollary 7.5 (p. 97) in degrees n >= 2; obtained there from Corollary 6.10 (p. 91) and Theorem 7.4.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem norm_residue_ker_le_of_two_le (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) (hn : 2 ≤ n)
    (φ : MilnorK F n →+ H F n) (hφ : ∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a)
    (x : MilnorK F n) (hx : φ x = 0) : ∃ y : MilnorK F n, x = 2 • y := by sorry
end MilnorConjecture
