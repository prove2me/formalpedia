-- Prove2me | Theorems.Thm_MasulloGRH_s_adele_quotient_compact_divisible
-- name    : MasulloGRH.s_adele_quotient_compact_divisible
-- status  : Proved
-- author  : @koffie
-- created : 2026-11-21T12:40:34.245024+00:00
-- url     : https://prove2.me/theorems/62578054-92ad-4d02-a28c-134bb2c4ddc8
-- title:
--   Lemma A.1.5.1, corrected — $\mathcal O_{F,S}$ is a cocompact lattice in $\mathbb A_{F,S}$; the quotient is divisible, uniquely $n$-divisible iff $1/n\in\mathcal O_{F,S}$
-- statement:
--   Let $F$ be a number field, $S$ a finite set of places containing the Archimedean places, $\mathbb A_{F,S}=\prod_{v\in S}F_v$ the $S$-adele ring, $\mathcal O_{F,S}$ the ring of $S$-integers and $\iota_S\colon\mathcal O_{F,S}\to\mathbb A_{F,S}$ the diagonal embedding.
--
--   1. $\iota_S$ is a closed map when $\mathcal O_{F,S}$ carries the discrete topology: the image of every subset of $\mathcal O_{F,S}$ is closed in $\mathbb A_{F,S}$.
--   2. The image $\iota_S(\mathcal O_{F,S})$ is discrete.
--   3. The quotient $\mathbb A_{F,S}/\mathcal O_{F,S}$ is compact and Hausdorff.
--   4. $\mathbb A_{F,S}/\mathcal O_{F,S}$ is divisible: multiplication by every integer $n\ge1$ is surjective.
--   5. For $n\ge1$, multiplication by $n$ on $\mathbb A_{F,S}/\mathcal O_{F,S}$ is injective if and only if $1/n\in\mathcal O_{F,S}$, i.e. every place of $F$ above a prime dividing $n$ lies in $S$.
--
--   **Relation to the source.** This is the corrected form of `MasulloGRH.s_adele_class_group_compact` (Lemma A.1.5.1, strict exactness, (1), (2) and the last sentence of (3)), which is disproved: its last sentence, "in particular $\mathbb A_{F,S}/\mathcal O_{F,S}$ is naturally a $\mathbb Q$-vector space", is false, e.g. $[1/2]\ne0$ is $2$-torsion in $\mathbb R/\mathbb Z$ for $F=\mathbb Q$, $S=\{\infty\}$. Unique divisibility holds for $\mathbb A_F/F\cong(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v})/\mathcal O_{F,S}$ (see `MasulloGRH.adele_class_group_compact`), not for its quotient $\mathbb A_{F,S}/\mathcal O_{F,S}$. Parts 4 and 5 state exactly what survives: the quotient is divisible, and it is uniquely $n$-divisible precisely when $n$ is a unit in $\mathcal O_{F,S}$. Since $S$ is finite, it is never a $\mathbb Q$-vector space.
--
--   **Formalization Note** The set $S$ is represented by its finite part $S_f$. The identification of $(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v})/\mathcal O_{F,S}$ with $\mathbb A_F/F$ and the properness assertion of part (3) of the source are not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.5.2, Lemma A.1.5.1, eq. (A.1.5.4), pp. 543–544: strict exactness, parts (1), (2), and the corrected form of the last assertion of (3)

import Definitions.Def_MasulloGRH_SAdeles

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem s_adele_quotient_compact_divisible (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ A : Set F, A ⊆ (SIntegers Sf : Set F) → IsClosed (sDiagonal Sf '' A)) ∧
    DiscreteTopology (sIntegerLattice Sf) ∧
    CompactSpace (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    T2Space (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    (∀ n : ℕ, 0 < n → Function.Surjective
      (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x)) ∧
    (∀ n : ℕ, 0 < n → (Function.Injective
      (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x) ↔
        ((n : F)⁻¹ ∈ SIntegers Sf))) := by sorry

end MasulloGRH
