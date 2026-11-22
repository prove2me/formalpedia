-- Prove2me | Theorems.Thm_MasulloGRH_s_unit_theorem
-- name    : MasulloGRH.s_unit_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:37:50.644852+00:00
-- url     : https://prove2.me/theorems/3a6b4d10-c01c-4664-aeca-7c1478e46b66
-- title:
--   Theorem A.1.5.2 — compactness of $C_{F,S}^1$, the $S$-unit theorem and finiteness of $\mathrm{Pic}(\mathcal O_{F,S})$
-- statement:
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, and $S$ a finite set of places containing the Archimedean places, so that $|S|=r_1+r_2+|S_f|$. Let $C_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v})/\mathcal O_{F,S}^\times$ be the $S$-idele class group and $C_{F,S}^1$ the kernel of the $S$-idelic norm on it.
--
--   1. $C_{F,S}^1$ is closed and compact.
--   2. The group of $S$-units $\mathcal O_{F,S}^\times$ is finitely generated, and its quotient by the torsion subgroup is free of rank $|S|-1$.
--   3. The ideal class group of the ring of $S$-integers $\mathcal O_{F,S}$ is finite.
--
--   The $S$-unit theorem gives the lattice $\mathcal O_{F,S}^\times$ over which the $S$-local $\theta$-functions are sums.
--
--   **Formalization Note** $C_{F,S}$ is represented by its image in $C_F$, an open subgroup; item 1 is stated for the image of $C_{F,S}^1$, the classes of ideles of norm $1$ that are units at all finite places outside $S$. The rank statement is written as $\operatorname{rank}+1=r_1+r_2+|S_f|$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.5.3, Theorem A.1.5.2, p. 544

import Definitions.Def_MasulloGRH_SAdeles

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem s_unit_theorem (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (IsClosed ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
        (sIntegralIdeles Sf ∩ {g | ideleNorm g = 1})) ∧
      IsCompact ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
        (sIntegralIdeles Sf ∩ {g | ideleNorm g = 1}))) ∧
    (Group.FG (SUnits Sf) ∧
      Module.finrank ℤ (Additive (SUnits Sf ⧸ CommGroup.torsion (SUnits Sf))) + 1 =
        InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card) ∧
    Finite (ClassGroup (SIntegers Sf)) := by sorry

end MasulloGRH
