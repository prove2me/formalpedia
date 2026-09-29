-- Prove2me | Theorems.Thm_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue
-- name    : IsLocalRing.isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/e1f81577-abd3-5f96-bd43-847cab4b9fa2
-- title:
--   Fibre products in Schlessinger's category of Artinian local O-algebras
-- statement:
--   Let $O$ be a commutative local ring, with residue map $\mathrm{residue}\colon O \to k$ onto its residue field $k = \mathrm{ResidueField}\,O$. Let $A'$ and $A''$ be commutative Artinian local $O$-algebras equipped with ring homomorphisms $\mathrm{res}_{A'}\colon A' \to k$ and $\mathrm{res}_{A''}\colon A'' \to k$ whose composites with the structure maps $O \to A'$, $O \to A''$ are the residue map of $O$. Let $A$ be any commutative $O$-algebra with a ring homomorphism $\mathrm{res}_A\colon A \to k$, and let $q'\colon A' \to A$ and $q''\colon A'' \to A$ be $O$-algebra homomorphisms satisfying $\mathrm{res}_A \circ q' = \mathrm{res}_{A'}$ and $\mathrm{res}_A \circ q'' = \mathrm{res}_{A''}$ (all four rings living in a single universe). The conclusion concerns the equalizer subalgebra of the two $O$-algebra maps $A' \times A'' \to A$ obtained as the first projection followed by $q'$ and the second projection followed by $q''$, i.e. the fibre product $\{(a',a'') : q'(a') = q''(a'')\}$. It asserts three things: this subalgebra is a local ring; it is an Artinian ring; and the ring homomorphism from it to $k$ given by inclusion into $A' \times A''$, followed by the first projection, followed by $\mathrm{res}_{A'}$, is surjective.
--
--   This is the standard fact that Schlessinger's category of Artinian local $O$-algebras with residue field $k$ admits fibre products over an arbitrary $O$-algebra, the surjectivity clause recording that the fibre product again has residue field $k$. It supplies the concrete squares to which the gluing conditions on a deformation functor are applied, and is used in the construction of a hull and in the criterion for a deformation functor to be representable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue
    (O : Type u) [CommRing O] [IsLocalRing O]
    (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
    (resA' : A' →+* ResidueField O) (hc' : resA'.comp (algebraMap O A') = residue O)
    (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
    (resA'' : A'' →+* ResidueField O) (hc'' : resA''.comp (algebraMap O A'') = residue O)
    (A : Type u) [CommRing A] [Algebra O A] (resA : A →+* ResidueField O)
    (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
    (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA'') :
    IsLocalRing ↥(AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))) ∧
    IsArtinianRing ↥(AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))) ∧
    Function.Surjective (resA'.comp ((AlgHom.fst O A' A'').comp
      (AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))).val).toRingHom) := by sorry
