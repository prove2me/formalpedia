-- Prove2me | Theorems.Thm_MasulloGRH_s_adele_class_group_compact
-- name    : MasulloGRH.s_adele_class_group_compact
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:37:04.510962+00:00
-- url     : https://prove2.me/theorems/e93a05a5-b56f-47a8-bc24-7995b9e29ffb
-- title:
--   Lemma A.1.5.1 — $\mathcal O_{F,S}$ is discrete in $\mathbb A_{F,S}$ and $\mathbb A_{F,S}/\mathcal O_{F,S}$ is compact
-- statement:
--   Let $F$ be a number field, $S$ a finite set of places containing the Archimedean places, $\mathbb A_{F,S}=\prod_{v\in S}F_v$ the $S$-adele ring, $\mathcal O_{F,S}$ the ring of $S$-integers and $\iota_S\colon\mathcal O_{F,S}\to\mathbb A_{F,S}$ the diagonal embedding.
--
--   1. $\iota_S$ is a closed map when $\mathcal O_{F,S}$ carries the discrete topology: the image of every subset of $\mathcal O_{F,S}$ is closed in $\mathbb A_{F,S}$.
--   2. The image $\iota_S(\mathcal O_{F,S})$ is discrete.
--   3. The quotient $\mathbb A_{F,S}/\mathcal O_{F,S}$ is compact and Hausdorff.
--   4. $\mathbb A_{F,S}/\mathcal O_{F,S}$ is uniquely divisible, i.e. a $\mathbb Q$-vector space.
--
--   This is the $S$-local form of the compactness of $\mathbb A_F/F$.
--
--   **Formalization Note** The set $S$ is represented by its finite part $S_f$. The identification of $(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v})/\mathcal O_{F,S}$ with $\mathbb A_F/F$ and the properness assertion of part (3) of the source are not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.5.2, Lemma A.1.5.1, eq. (A.1.5.4), pp. 543–544: strict exactness, parts (1), (2) and the last assertion of (3)

import Definitions.Def_MasulloGRH_SAdeles

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem s_adele_class_group_compact (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ A : Set F, A ⊆ (SIntegers Sf : Set F) → IsClosed (sDiagonal Sf '' A)) ∧
    DiscreteTopology (sIntegerLattice Sf) ∧
    CompactSpace (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    T2Space (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    (∀ n : ℕ, 0 < n → Function.Bijective
      (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x)) := by sorry

end MasulloGRH
