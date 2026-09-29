-- Prove2me | Theorems.Thm_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ
-- name    : ModularCurve.arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/93d10332-0154-5bba-8c45-851c4f8f9b0a
-- title:
--   Arithmetic Frobenius sends a place to its coefficientwise twist
-- statement:
--   Let $q$ be a prime, $K$ a perfect field of characteristic $q$, and $N$ a nonzero natural number. Let $F =$ `modularFunctionFieldC K N` be the intermediate field of $K((X))$ (Laurent series over $K$, i.e. Hahn series with integer exponents) generated over $K$ by the two series `jqModC K` $= X^{-1}\cdot(E_4^3\,\eta^{-24})$, the reduction to $K$ of the $q$-expansion of the modular invariant, and `jqNModC K N`, its image under `qExpand K N`, the ring homomorphism multiplying all exponents by $N$. Let $\iota,\iota' : F \to K((X))$ be $K$-algebra homomorphisms such that $\iota'$ and $\iota$ agree on each of the two generators up to `coeffMap (frobenius K q)`, the coefficientwise $q$-th power map on Laurent series: $\iota'(\bar j) = \iota(\bar j)^{(q)}$ and $\iota'(\bar j_N) = \iota(\bar j_N)^{(q)}$. Let $w, w'$ be places of $F$ over $K$, each given by a valuation subring of $F$ containing $K$, distinct from $F$ and a principal ideal ring, and assume that $x$ lies in the valuation subring of $w$ exactly when the order of $\iota(x)$ is nonnegative, and in that of $w'$ exactly when the order of $\iota'(x)$ is nonnegative. Then the arithmetic Frobenius `arithFrobC q K N`, the semilinear automorphism of $F$ over $K$ given by the pair consisting of the coefficientwise $q$-th power automorphism of $F$ and the Frobenius of $K$, carries $w$ to $w'$ under the induced action on places.
--
--   This identifies the effect of the arithmetic Frobenius on the places of the geometric modular function field of level $N$ in terms of Laurent expansions: twisting an embedding coefficientwise by the $q$-th power map moves the associated place by Frobenius. It is used in the analysis of fibres and supersingular loci, through [`ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ`](thm.html#ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ), and relies only on the fact that a $K$-algebra homomorphism out of `modularFunctionFieldC K N` is determined by its values on the two generators ([`ModularCurve.modularFunctionFieldC_algHom_ext`](thm.html#ModularCurve.modularFunctionFieldC_algHom_ext)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ.lean

import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ
    (q N : ℕ) [NeZero N] (K : Type*) [Field K] [Fact q.Prime] [CharP K q] [PerfectField K]
    (ι ι' : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (hj : ι' ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩))
    (hjN : ι' ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩))
    (w w' : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))
    (hw : ∀ x, x ∈ w.toValuationSubring ↔ 0 ≤ (ι x).order)
    (hw' : ∀ x, x ∈ w'.toValuationSubring ↔ 0 ≤ (ι' x).order) :
    ModularCurve.arithFrobC q K N • w = w' := by sorry
