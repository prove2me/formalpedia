-- Prove2me | Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
-- name    : IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/fd781c8e-eece-5e72-8539-9e79e21ff53c
-- title:
--   Isomorphic local rings have isomorphic maximal-adic completions
-- statement:
--   Let $R$ and $S$ be commutative rings, each equipped with the typeclass assumption of being a local ring (so each has a distinguished maximal ideal `IsLocalRing.maximalIdeal`), and let $e : R \simeq S$ be a ring isomorphism. The assertion is that there exists a ring isomorphism $\hat e$ from the adic completion of $R$ with respect to $\mathfrak m_R =$ `IsLocalRing.maximalIdeal R` onto the adic completion of $S$ with respect to $\mathfrak m_S =$ `IsLocalRing.maximalIdeal S` — in Mathlib's sense, the ring of families $(x_n)$ with $x_n \in R/\mathfrak m_R^n$ compatible under the transition maps — such that for every $r \in R$ the image under $\hat e$ of the canonical structure map (the `algebraMap`) applied to $r$ equals the canonical structure map of $S$ applied to $e(r)$. Thus $\hat e$ is compatible with the completion maps: $\hat e \circ (R \to \widehat R_{\mathfrak m_R}) = (S \to \widehat S_{\mathfrak m_S}) \circ e$. Only existence of such an $\hat e$ is asserted; no uniqueness, continuity or further naturality statement is made.
--
--   This is the functoriality of maximal-adic completion along an isomorphism of local rings, in the form needed when no general functoriality for ring maps between different rings and ideals is available. It is used to transport presentations of node rings of modular curves along an identification of a local ring with the same ring read in a larger level field, and is cited by several statements about Drinfeld charts and integral models at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    ∃ ê : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (e r) := by sorry
