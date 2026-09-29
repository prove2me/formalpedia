-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
-- name    : NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/638a2e53-f34e-55fe-9fc7-1e793d8a12cf
-- title:
--   Order of the decomposition group equals ef
-- statement:
--   Let $K$ and $K''$ be number fields (types in `Type`, each with a field structure and a `NumberField` instance), with $K''$ an algebra over $K$ such that the extension $K''/K$ is Galois, and let $w''$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_{K''}$, i.e. a nonzero prime ideal of $\mathcal{O}_{K''}$. Write $G = K'' \simeq_{\mathrm{alg}[K]} K''$ for the group of $K$-algebra automorphisms of $K''$, and let `decomp K K'' w''` denote the decomposition subgroup of $G$ attached to the valuation subring of the $w''$-adic valuation on $K''$, that is, the subgroup of those automorphisms that preserve that valuation subring. The assertion is that the cardinality (as a natural number, via `Nat.card`) of this subgroup equals the product of the ramification index and the inertia degree, in Mathlib's primed forms `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` taking two ideals and no ring homomorphism argument, of the pair consisting of the ideal underlying $w''$ contracted to $\mathcal{O}_K$ (the prime `HeightOneSpectrum.under (𝓞 K) w''`) and the ideal $w''.\mathrm{asIdeal}$ itself. Thus $|D(w'' \mid K)| = e(w''\mid w)\, f(w''\mid w)$ for the prime $w$ of $K$ below $w''$.
--
--   This is the classical formula for the order of the decomposition group of a prime in a Galois extension of number fields, the group-theoretic counterpart of the identity $[K''_{w''}:K_w] = ef$. It is used in the local analysis of places in towers of number fields, for instance in constructing elements of prescribed valuation in unramified situations and in computations with local Artin symbols and Herbrand-style arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
    (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K''] [IsGalois K K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    Nat.card (decomp K K'' w'') =
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w'').asIdeal w''.asIdeal *
        Ideal.inertiaDeg' (HeightOneSpectrum.under (𝓞 K) w'').asIdeal w''.asIdeal := by sorry
