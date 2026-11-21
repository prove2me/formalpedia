-- Prove2me | Theorems.Thm_MasulloGRH_idele_class_group_norm_one_compact
-- name    : MasulloGRH.idele_class_group_norm_one_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:36:36.049643+00:00
-- url     : https://prove2.me/theorems/f80f5cb3-ec2c-4da0-ab45-016ced9a762c
-- title:
--   Theorem A.1.4.3 — compactness of $C_F^1$, the unit theorem and finiteness of the class group
-- statement:
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, and let $C_F^1$ be the subgroup of the idele class group $C_F$ consisting of the classes of ideles of idelic norm $1$.
--
--   1. $C_F^1$ is a closed and compact subgroup of $C_F$.
--   2. The unit group $\mathcal O_F^\times$ is finitely generated, and its quotient by the torsion subgroup is free of rank $r_1+r_2-1$.
--   3. The ideal class group of $\mathcal O_F$ is finite.
--
--   Item 1 is the adelic form of items 2 and 3 taken together, which are Dirichlet's unit theorem and the finiteness of the class number.
--
--   **Formalization Note** The rank statement is written as $\operatorname{rank}+1=r_1+r_2$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.4.1, Theorem A.1.4.3, pp. 542–543

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem idele_class_group_norm_one_compact (F : Type*) [Field F] [NumberField F] :
    (IsClosed ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' {g | ideleNorm g = 1}) ∧
      IsCompact ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' {g | ideleNorm g = 1})) ∧
    (Group.FG (𝓞 F)ˣ ∧
      Module.finrank ℤ (Additive ((𝓞 F)ˣ ⧸ CommGroup.torsion (𝓞 F)ˣ)) + 1 =
        InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F) ∧
    Finite (ClassGroup (𝓞 F)) := by sorry

end MasulloGRH
