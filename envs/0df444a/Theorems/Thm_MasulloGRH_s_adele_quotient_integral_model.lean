-- Prove2me | Theorems.Thm_MasulloGRH_s_adele_quotient_integral_model
-- name    : MasulloGRH.s_adele_quotient_integral_model
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:46.291173+00:00
-- url     : https://prove2.me/theorems/18b31a54-2869-470c-8f8e-8ca0e55c226a
-- title:
--   Lemma A.1.5.1(3), corrected — $(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v})/\mathcal O_{F,S}\cong\mathbb A_F/F$, with a proper quotient map onto $\mathbb A_{F,S}/\mathcal O_{F,S}$
-- statement:
--   **Lemma A.1.5.1(3), corrected — the $S$-integral model of $\mathbb A_F/F$ and its proper projection onto $\mathbb A_{F,S}/\mathcal O_{F,S}$.**
--
--   Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places, $\mathbb A_{F,S}=\prod_{v\in S}F_v$ the $S$-adele ring and $\mathcal O_{F,S}$ the ring of $S$-integers. Put
--   $$\mathbb A_F(S)=\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v}=\{a\in\mathbb A_F:\ a_v\in\mathcal O_{F_v}\ \text{for all }v\notin S\},$$
--   a subring of the adele ring $\mathbb A_F$, with the subspace topology. The ring $\mathcal O_{F,S}$ is embedded diagonally in $\mathbb A_F(S)$ and in $\mathbb A_{F,S}$, the field $F$ is embedded diagonally in $\mathbb A_F$, and all quotients carry the quotient topology. Then:
--
--   1. The inclusion $\mathbb A_F(S)\subseteq\mathbb A_F$ induces an isomorphism of topological groups
--   $$\mathbb A_F(S)/\mathcal O_{F,S}\ \xrightarrow{\ \sim\ }\ \mathbb A_F/F .$$
--   2. The projection $\mathbb A_F(S)\to\mathbb A_{F,S}$, $a\mapsto(a_v)_{v\in S}$, induces a homomorphism
--   $$\pi\colon\ \mathbb A_F(S)/\mathcal O_{F,S}\longrightarrow\mathbb A_{F,S}/\mathcal O_{F,S}$$
--   which is proper, continuous, open and surjective, i.e. a proper quotient homomorphism of topological groups.
--
--   This is the bridge between the global additive quotient $\mathbb A_F/F$ and its $S$-local analog $\mathbb A_{F,S}/\mathcal O_{F,S}$; when $S$ is the set of Archimedean places, part 1 is the isomorphism (A.1.2.2) of Lemma A.1.2.1. It completes Lemma A.1.5.1, whose strict exactness and parts (1), (2) are `MasulloGRH.s_adele_quotient_compact_divisible`.
--
--   **Deviation from the source.** The last sentence of Lemma A.1.5.1(3), "In particular, $\mathbb A_{F,S}/\mathcal O_{F,S}$ is naturally a $\mathbb Q$-vector space", is false (for $F=\mathbb Q$ and $S=\{\infty\}$ the quotient is $\mathbb R/\mathbb Z$, which has $2$-torsion) and is not part of this statement. The source's "isomorphic to $\mathbb A_F/F$ under the continuous injective homomorphism induced by" the inclusion is stated as an isomorphism of topological groups, and "quotient homomorphism" as a continuous open surjection.
--
--   **Formalization Note.** $S$ is represented by the finite set $S_f$ of its finite places. $\mathbb A_F(S)$ is the subring `RiemannMasullo.integralAdelesOutside F Sf` of `AdeleRing (𝓞 F) F`, and the diagonal image of $\mathcal O_{F,S}$ in it is the range of `RiemannMasullo.integralAdeleDiagonal F Sf`; $\mathbb A_{F,S}$ is `SAdeleRing F Sf`, the product of the infinite adele ring with $\prod_{v\in S_f}F_v$, and the diagonal image of $\mathcal O_{F,S}$ in it is `sIntegerLattice Sf`; $F\subseteq\mathbb A_F$ is `AdeleRing.principalSubgroup`. "Proper" is Mathlib's `IsProperMap` (continuous and universally closed), and `IsOpenQuotientMap` means surjective, continuous and open.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 543, Lemma A.1.5.1(3)

import Mathlib
import Definitions.Def_RiemannMasullo_IntegralAdeleDiagonal
import Definitions.Def_MasulloGRH_SAdeles

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem s_adele_quotient_integral_model (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    let I := RiemannMasullo.integralAdelesOutside F Sf
    let D : AddSubgroup I := (RiemannMasullo.integralAdeleDiagonal F Sf).toAddMonoidHom.range
    (∃ e : (I ⧸ D) ≃ₜ+ (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F),
      ∀ x : I, e (QuotientAddGroup.mk x) = QuotientAddGroup.mk (x : AdeleRing (𝓞 F) F)) ∧
    ∃ π : (I ⧸ D) →+ (SAdeleRing F Sf ⧸ sIntegerLattice Sf),
      IsProperMap π ∧ IsOpenQuotientMap π ∧
      ∀ x : I, π (QuotientAddGroup.mk x) =
        QuotientAddGroup.mk
          (((x : AdeleRing (𝓞 F) F).1, fun v : Sf => (x : AdeleRing (𝓞 F) F).2 v) :
            SAdeleRing F Sf) := by sorry

end MasulloGRH
