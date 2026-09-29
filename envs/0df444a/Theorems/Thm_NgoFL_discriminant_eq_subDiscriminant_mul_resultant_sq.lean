-- Prove2me | Theorems.Thm_NgoFL_discriminant_eq_subDiscriminant_mul_resultant_sq
-- name    : NgoFL.discriminant_eq_subDiscriminant_mul_resultant_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T01:37:52.171833+00:00
-- url     : https://prove2.me/theorems/4e601c41-fa7f-48b6-9f95-1fe9fd28bc71
-- title:
--   1.10.3: $\nu^* D_G = D_H \cdot (R^G_H)^2$ up to sign
-- statement:
--   Keep the notation of Lemma 1.10.2: a root system $\Phi$, a subsystem $\Phi_H$, and a set
--   $\Lambda$ of representatives of the pairs of opposite roots outside $\Phi_H$. Because
--   $\Phi - \Phi_H$ is the disjoint union of $\Lambda$ and $-\Lambda$, the discriminant factors as
--
--   $$ D_G \;=\; \prod_{\alpha \in \Phi} d\alpha
--        \;=\; (-1)^{|\Lambda|} \,\Bigl(\prod_{\alpha \in \Phi_H} d\alpha\Bigr)
--          \Bigl(\prod_{\alpha \in \Lambda} d\alpha\Bigr)^{2}
--        \;=\; (-1)^{|\Lambda|}\, D_H \cdot (R^G_H)^2 . $$
--
--   This is the function-level form of Ngo's identity of divisors on the space of characteristic
--   polynomials of $H$,
--
--   $$ \nu^* \mathfrak{D}_G \;=\; \mathfrak{D}_H + 2\,\mathfrak{R}^G_H , $$
--
--   in which the unit $(-1)^{|\Lambda|}$ disappears; here it is kept explicitly because the
--   statement is an equality of functions rather than of divisors. Together with Lemma 1.10.2,
--   which guarantees that $R^G_H$ is $W_H$-invariant and therefore descends, this is the conclusion
--   of §1.10, and it is what produces the exponent in the transfer factor.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, p. 21, 1.10.3 ($\nu^* \mathfrak{D}_G = \mathfrak{D}_H + 2 \mathfrak{R}^G_H$)

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

namespace NgoFL

theorem discriminant_eq_subDiscriminant_mul_resultant_sq {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (P : RootPairing ι R M N) (s L : Finset ι) (hL : IsHalfSystem P sᶜ L) (x : N) :
    discriminant P x
      = (-1) ^ L.card * (subDiscriminant P s x * resultant P L x ^ 2) := by sorry

end NgoFL
