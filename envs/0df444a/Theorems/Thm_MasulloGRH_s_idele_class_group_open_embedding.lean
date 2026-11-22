-- Prove2me | Theorems.Thm_MasulloGRH_s_idele_class_group_open_embedding
-- name    : MasulloGRH.s_idele_class_group_open_embedding
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:42.406798+00:00
-- url     : https://prove2.me/theorems/45e1b4b2-acb5-4706-929d-737bd84b6e6a
-- title:
--   Eq. (A.1.5.7) — the $S$-idele class group $C_{F,S}$ is Hausdorff locally compact and embeds as an open subgroup of $C_F$
-- statement:
--   **The $S$-idele class group $C_{F,S}$ is a Hausdorff locally compact group, embedded as an open subgroup of $C_F$** (eq. (A.1.5.7) of the source).
--
--   Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places, $\mathcal O_{F,S}^\times$ the group of $S$-units, and
--   $$J_S=\mathrm{GL}_1\Big(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v}\Big)=\{g\in\mathrm{GL}_1(\mathbb A_F):\ |g_v|_v=1\ \text{for all }v\notin S\}$$
--   the group of ideles that are units at every place outside $S$, with the topology induced from the idele group $\mathrm{GL}_1(\mathbb A_F)$. The $S$-idele class group is the quotient
--   $$C_{F,S}=J_S/\mathcal O_{F,S}^\times$$
--   by the diagonally embedded $S$-units, with the quotient topology, and $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$ is the idele class group. Then:
--
--   1. $J_S$ is an open subgroup of $\mathrm{GL}_1(\mathbb A_F)$.
--   2. $F^\times\cap J_S=\mathcal O_{F,S}^\times$: the principal idele of $\xi\in F^\times$ lies in $J_S$ if and only if $\xi$ is an $S$-unit.
--   3. $C_{F,S}$ is Hausdorff and locally compact.
--   4. The homomorphism
--   $$C_{F,S}=J_S/\mathcal O_{F,S}^\times\longrightarrow C_F$$
--   induced by the inclusion $J_S\subseteq\mathrm{GL}_1(\mathbb A_F)$ is an open embedding of topological groups (injective, continuous and open), and its image is the set of classes of the ideles in $J_S$.
--
--   Statement 3 is the assertion made in the source right after (A.1.5.7). Statements 1, 2 and 4 are the standard facts behind it: they identify $C_{F,S}$, as a topological group, with an open subgroup of $C_F$, which is the form in which $C_{F,S}$ and its norm-one subgroup $C^1_{F,S}$ enter Theorem A.1.5.2 (`MasulloGRH.s_unit_theorem`).
--
--   **Formalization Note.** $S$ is represented by the finite set $S_f$ of its finite places. $J_S$ is the subgroup `U` of `IdeleGroup F` whose underlying set is `sIntegralIdeles Sf`; this determines `U`. $C_{F,S}$ is `U ⧸ (principalIdeles F).subgroupOf U`, the quotient of $J_S$ by $F^\times\cap J_S$, which by statement 2 is the quotient by the $S$-units. The image in statement 4 is `sIdeleClasses Sf`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 544, §A.1.5.3, eq. (A.1.5.7) and the sentence after it

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem s_idele_class_group_open_embedding (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ U : Subgroup (IdeleGroup F),
      (U : Set (IdeleGroup F)) = sIntegralIdeles Sf ∧
      IsOpen (U : Set (IdeleGroup F)) ∧
      (∀ ξ : Fˣ, principalIdele F ξ ∈ U ↔ ξ ∈ SUnits Sf) ∧
      T2Space (U ⧸ (principalIdeles F).subgroupOf U) ∧
      LocallyCompactSpace (U ⧸ (principalIdeles F).subgroupOf U) ∧
      ∃ j : (U ⧸ (principalIdeles F).subgroupOf U) →* IdeleClassGroup F,
        Topology.IsOpenEmbedding j ∧
        (∀ u : U, j (QuotientGroup.mk u) = QuotientGroup.mk (u : IdeleGroup F)) ∧
        Set.range j = sIdeleClasses Sf := by sorry

end MasulloGRH
