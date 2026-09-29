-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp
-- name    : NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/53c3bba3-91a1-5447-935d-412165ab6d38
-- title:
--   Decomposition group over ℚ versus over an intermediate field
-- statement:
--   Let $E$ and $F$ be number fields with a ring homomorphism structure making $F$ an $E$-algebra, and assume that $F$ is Galois both over $\mathbb{Q}$ and over $E$. Let $w$ be a height-one prime of the ring of integers $\mathcal{O}_F$, and let $q$ be a prime number whose image in $\mathcal{O}_F$ lies in the prime ideal $w$. Write $v =$ the contraction (`Ideal.comap`) of $w$ along $\mathcal{O}_E \to \mathcal{O}_F$, a prime of $\mathcal{O}_E$. For a base field $K$ and $w$ as above, [`NumberField.PlaceDecomp.decomp K F w`](def/NumberField_PlaceDecompositionAction.html#L82) denotes the decomposition subgroup of $F \simeq_{\mathrm{alg}[K]} F$ attached to the valuation subring of the $w$-adic valuation of $F$, i.e. the subgroup of $K$-algebra automorphisms of $F$ that stabilise that valuation subring. The assertion is the equality of natural numbers
--   $$\#\,\mathrm{decomp}(\mathbb{Q}, F, w) = e\big((q)\mathbb{Z},\, v\big)\cdot f\big((q)\mathbb{Z},\, v\big)\cdot \#\,\mathrm{decomp}(E, F, w),$$
--   where $e$ and $f$ are `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` of the ideal $\mathbb{Z}\cdot q$ at the prime $v$ of $\mathcal{O}_E$, and the cardinalities are `Nat.card` of the two decomposition subgroups.
--
--   This is the multiplicativity of the local degree in a tower: the decomposition group of $w$ in $\mathrm{Gal}(F/\mathbb{Q})$ has order $[E_v:\mathbb{Q}_q]$ times the order of the decomposition group of $w$ in $\mathrm{Gal}(F/E)$. It records the factor by which restriction from $\mathrm{Gal}(F/\mathbb{Q})$ to $\mathrm{Gal}(F/E)$ rescales local invariants, and is used in the group-cohomological computation of local invariants of classes restricted along such a tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois ℚ F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) (q : ℕ) [Fact q.Prime] (hq : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w) =
      Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
        Ideal.inertiaDeg' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
        Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by sorry
