-- Prove2me | Theorems.Thm_MilnorConjecture_milnor_conjecture
-- name    : MilnorConjecture.milnor_conjecture
-- status  : Open
-- author  : @vatsj
-- created : 2026-09-24T21:11:53.163384+00:00
-- url     : https://prove2.me/theorems/73a40952-d2f1-49b9-8bfd-fd13c6c2ac6c
-- title:
--   Milnor conjecture: $K^M_n(F)/2 \cong H^n(F,\mathbb{Z}/2)$
-- statement:
--   **Milnor conjecture** (Voevodsky 2003, Corollary 7.5). Let $F$ be a field of characteristic different from $2$ and let $n \ge 0$. Then there exists a group homomorphism
--   $$\varphi : K^M_n(F) \longrightarrow H^n(F,\mathbb{Z}/2)$$
--   such that
--
--   1. $\varphi\{a_1,\dots,a_n\} = \delta a_1\cup\cdots\cup\delta a_n$ (the Galois symbol) for all $a_1,\dots,a_n \in F^\times$;
--   2. $\varphi$ is surjective;
--   3. $\ker\varphi = 2\,K^M_n(F)$, i.e. $\varphi(x) = 0$ if and only if $x = 2y$ for some $y\in K^M_n(F)$.
--
--   Since symbols generate $K^M_n(F)$, condition 1 determines $\varphi$: it is the norm residue homomorphism, and conditions 2 and 3 say that it induces an isomorphism $K^M_n(F)/2 \cong H^n(F,\mathbb{Z}/2)$. Here $H^n(F,\mathbb{Z}/2)$ is continuous cohomology of $\operatorname{Gal}(F^{\mathrm{sep}}/F)$, which equals étale cohomology of $\operatorname{Spec} F$ with $\mathbb{Z}/2 \cong \mu_2$ coefficients.
--
--   **Formalization Note** The existence of $\varphi$ (well-definedness of the norm residue map on the Steinberg relations) is part of the statement. $F$ ranges over `Type`, and $\operatorname{char} F\neq 2$ is `[NeZero (2 : F)]`.
-- source:
--   V. Voevodsky, Motivic cohomology with Z/2-coefficients, Publ. Math. IHES 98 (2003), 59-104, https://doi.org/10.1007/s10240-003-0010-6, p. 97, Section 7 (Main theorem, starting p. 95), Corollary 7.5: for k of characteristic not 2, the norm residue homomorphisms K^M_w(k)/2 -> H^w_et(k, Z/2) are isomorphisms for all w >= 0.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem milnor_conjecture (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) :
    ∃ φ : MilnorK F n →+ H F n,
      (∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a) ∧
      Function.Surjective φ ∧
      ∀ x : MilnorK F n, φ x = 0 ↔ ∃ y : MilnorK F n, x = 2 • y := by sorry
end MilnorConjecture
