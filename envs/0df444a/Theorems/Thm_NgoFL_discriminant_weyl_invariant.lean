-- Prove2me | Theorems.Thm_NgoFL_discriminant_weyl_invariant
-- name    : NgoFL.discriminant_weyl_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T00:30:21.287835+00:00
-- url     : https://prove2.me/theorems/706c428e-65ef-4b20-b3c8-2a022b5d540d
-- title:
--   The discriminant $D_G = \prod_{\alpha \in \Phi} d\alpha$ is $W$-invariant
-- statement:
--   Let $\Phi$ be the root system of a split reductive group $G$ with Cartan subalgebra
--   $\mathfrak{t}$, and for each root $\alpha$ let $d\alpha$ be its differential, a linear form on
--   $\mathfrak{t}$. Ngo's discriminant is
--
--   $$ D_G \;=\; \prod_{\alpha \in \Phi} d\alpha . $$
--
--   The statement is that $D_G$ is invariant under the Weyl group: $D_G(wx) = D_G(x)$ for every
--   $w \in W$ and every $x \in \mathfrak{t}$.
--
--   This is the assertion, made in passing at the start of §1.10 ("qui est clairement un element
--   $W$-invariant de cette algebre de polynomes"), that lets $D_G$ descend to a function on the
--   space $\mathfrak{c} = \mathfrak{t}/\!/W$ of characteristic polynomials, and hence to define the
--   discriminant divisor $\mathfrak{D}_G$ of $\mathfrak{c}$ whose complement is the regular
--   semisimple locus. The reason is that $W$ permutes $\Phi$, so the factors of the product are
--   permuted among themselves.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, p. 20, §1.10 ($D_G = \prod_{\alpha \in \Phi} d\alpha$ is $W$-invariant; Lemme 1.10.1)

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

namespace NgoFL

theorem discriminant_weyl_invariant {ι R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Fintype ι] (P : RootPairing ι R M N)
    (w : N ≃ₗ[R] N) (hw : w ∈ weylSubgroup P Set.univ) (x : N) :
    discriminant P (w x) = discriminant P x := by sorry

end NgoFL
