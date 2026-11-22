-- Prove2me | Theorems.Thm_MasulloGRH_ideleGroup_quotient_principal_sup_sIntegral_equiv_classGroup
-- name    : MasulloGRH.ideleGroup_quotient_principal_sup_sIntegral_equiv_classGroup
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:55.849453+00:00
-- url     : https://prove2.me/theorems/1fd093ae-e8a2-417f-ba32-6e9e8f225319
-- title:
--   Lemma D.1.10.1(3) — the cokernel of $C_{F,S}\to C_F$ is the class group of the $S$-integers: $\mathrm{GL}_1(\mathbb A_F)/F^\times J_S\cong\mathrm{Pic}(\mathcal O_{F,S})$
-- statement:
--   **The cokernel of $C_{F,S}\to C_F$ is the ideal class group of the ring of $S$-integers** (Lemma D.1.10.1(3)).
--
--   Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places, $\mathcal O_{F,S}=\{\xi\in F:\ |\xi|_v\le1\ \text{for all }v\notin S\}$ the ring of $S$-integers and $\mathrm{Pic}(\mathcal O_{F,S})$ its ideal class group. Let
--   $$J_S=\mathrm{GL}_1\Big(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v}\Big)=\{g\in\mathrm{GL}_1(\mathbb A_F):\ |g_v|_v=1\ \text{for all }v\notin S\}$$
--   be the group of ideles that are units at every place outside $S$, where $F_v$ is the completion of $F$ at $v$, $\mathcal O_{F_v}$ its ring of integers for finite $v$, and $\mathbb A_{F,S}=\prod_{v\in S}F_v$ (as in (A.1.5.1) of the source); let $C_{F,S}=J_S/\mathcal O_{F,S}^\times$ be the $S$-idele class group. The inclusion $J_S\subseteq\mathrm{GL}_1(\mathbb A_F)$ induces a continuous injective open homomorphism
--   $$i_{F,S}\colon C_{F,S}\longrightarrow C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times,$$
--   whose image is the subgroup $F^\times J_S/F^\times$ of classes of ideles in $J_S$.
--
--   **Statement.** The cokernel of $i_{F,S}$ is isomorphic to the ideal class group of $\mathcal O_{F,S}$:
--   $$C_F/i_{F,S}(C_{F,S})\ =\ \mathrm{GL}_1(\mathbb A_F)\big/\big(F^\times\cdot J_S\big)\ \cong\ \mathrm{Pic}(\mathcal O_{F,S}).$$
--
--   Since $\mathrm{Pic}(\mathcal O_{F,S})$ is finite (Theorem A.1.5.2 of the source), $i_{F,S}$ identifies $C_{F,S}$ with an open subgroup of finite index of $C_F$; for $S$ the set of Archimedean places this is the classical description $\mathrm{GL}_1(\mathbb A_F)/F^\times\big(\prod_{v\mid\infty}F_v^\times\times\prod_{v\nmid\infty}\mathcal O_{F_v}^\times\big)\cong\mathrm{Pic}(\mathcal O_F)$ of the ideal class group. The source uses the lemma to transfer its families of seminorms from $\mathcal S(C_F)$ to $\mathcal S(C_{F,S})$.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. $J_S$ is the subgroup `U` of `IdeleGroup F` whose underlying set is the platform set `sIntegralIdeles Sf` (this determines `U`), and $F^\times\cdot J_S$ is the join `principalIdeles F ⊔ U`. The cokernel is written as the quotient `IdeleGroup F ⧸ (principalIdeles F ⊔ U)` of the idele group, which is the quotient of $C_F$ by the image of $C_{F,S}$. $\mathrm{Pic}(\mathcal O_{F,S})$ is Mathlib's `ClassGroup (SIntegers Sf)` of the platform subalgebra `SIntegers Sf` of $F$. The statement is the existence of a group isomorphism (`≃*`); the cokernel is discrete because the image of $i_{F,S}$ is open. That $i_{F,S}$ is an open embedding with image the classes of $J_S$ is the platform statement `MasulloGRH.s_idele_class_group_open_embedding`. Related platform statements (none of them is the present one): for $S$ the set of Archimedean places, `NumberField.TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber` gives the index $[\mathrm{GL}_1(\mathbb A_F):F^\times J_S]=h_F$; `IsDedekindDomain.FiniteAdeleRing.nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range` is the finite-idelic presentation of the class group of a Dedekind domain; `IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff` describes, through the content map, the product of $F^\times$ with the finite ideles that are units outside a set $T$ of primes; and `NumberField.SClassGroup.pic_localization_exact` is the localization exact sequence for the class groups of rings of $S$-integers. The present statement is the $S$-version inside the ideles of $F$ (the cokernel of $C_{F,S}\to C_F$); the platform subgroup `NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F ↑Sf` has the same elements as `sIntegralIdeles Sf` (`NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 784, Lemma D.1.10.1(3), eq. (D.1.10.2)

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem ideleGroup_quotient_principal_sup_sIntegral_equiv_classGroup (F : Type*) [Field F]
    [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ U : Subgroup (IdeleGroup F), (U : Set (IdeleGroup F)) = sIntegralIdeles Sf ∧
      Nonempty ((IdeleGroup F ⧸ (principalIdeles F ⊔ U)) ≃* ClassGroup (SIntegers Sf)) := by
  sorry

end MasulloGRH
