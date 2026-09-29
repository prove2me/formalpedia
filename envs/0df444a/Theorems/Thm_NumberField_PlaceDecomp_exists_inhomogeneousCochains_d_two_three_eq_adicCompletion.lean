-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion
-- name    : NumberField.PlaceDecomp.exists_inhomogeneousCochains_d_two_three_eq_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/5a9ea192-b235-566a-984d-cf92a413c2a1
-- title:
--   Vanishing of H³(D_w, (K_w)^×) at cochain level
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an extension of $E$ that is Galois, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$. Write $D_w :=$ [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82) for the decomposition subgroup of $K \simeq_{\text{alg}[E]} K$ attached to the valuation subring of the $w$-adic valuation of $K$, and let $A$ be the representation `Rep.ofMulDistribMulAction` of $D_w$ on the unit group $((K_w)^\times$ of the $w$-adic completion $K_w$, i.e. the multiplicative group of units written additively with its natural $D_w$-action, regarded as an object of `Rep ℤ D_w`. The assertion is: for every inhomogeneous $3$-cochain $u \colon D_w^{3} \to A$, that is every function from $\mathrm{Fin}\,3 \to D_w$ to $A$, such that the differential $d^{3,4}$ of the complex `inhomogeneousCochains A` kills $u$, there exists an inhomogeneous $2$-cochain $c \colon D_w^{2} \to A$ with $d^{2,3} c = u$. Thus every $3$-cocycle of $D_w$ with values in $(K_w)^\times$ is a coboundary, which is the statement $H^3(D_w, (K_w)^\times) = 0$ phrased at the level of cochains.
--
--   This is the degree-three instance of Tate's theorem for the local class formation: the cup product with the local fundamental class identifies $\hat H^{q}(S,\mathbb{Z})$ with $\hat H^{q+2}(S,(K_w)^\times)$ for subgroups $S \le D_w$, and at $q = 1$ the left-hand side $\mathrm{Hom}(D_w,\mathbb{Z})$ vanishes because $D_w$ is finite. The cochain-level formulation is what is used downstream, in [`NumberField.LevelArith.exists_inhomogeneousCochains_d_two_three_eq_sIdele`](thm.html#NumberField.LevelArith.exists_inhomogeneousCochains_d_two_three_eq_sIdele).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_inhomogeneousCochains_d_two_three_eq_adicCompletion
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (u : (Fin 3 → ↥(NumberField.PlaceDecomp.decomp E K w)) → Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hu : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)).d 3 4).hom u = 0) :
    ∃ c : (Fin 2 → ↥(NumberField.PlaceDecomp.decomp E K w)) → Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ,
      ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)).d 2 3).hom c = u := by sorry
