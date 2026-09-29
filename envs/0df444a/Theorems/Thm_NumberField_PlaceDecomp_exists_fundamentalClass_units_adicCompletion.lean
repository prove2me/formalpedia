-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion
-- name    : NumberField.PlaceDecomp.exists_fundamentalClass_units_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/578e0842-d224-58f0-a2c4-f5ac1401ff94
-- title:
--   Local fundamental class for the decomposition group at w
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$. Write $D_w =$ `decomp E K w` for the decomposition subgroup of $K \simeq_{\mathrm{alg}[E]} K$ attached to $w$, namely the decomposition subgroup over $E$ of the valuation subring of the $w$-adic valuation of $K$, and let $A$ be the $w$-adic completion $K_w$ of $K$ at $w$ viewed, through its multiplicative distributive $D_w$-action on units, as the $\mathbb{Z}$-linear representation `Rep.ofMulDistribMulAction` of $D_w$ on $K_w^{\times}$ (written additively). The assertion is that there exists a class $u \in H^2(D_w, A)$ such that, simultaneously: (i) for every subgroup $S \le D_w$, the group cohomology $H^1(S, A)$ of the restriction of $A$ along $S \hookrightarrow D_w$ is a zero object; (ii) for every subgroup $S \le D_w$ that is finite, $H^2(S, A)$ has cardinality equal to the order of $S$; and (iii) for every subgroup $S \le D_w$, the image of $u$ under the restriction map in degree $2$ generates $H^2(S, A)$ as a $\mathbb{Z}$-module, i.e. its $\mathbb{Z}$-span is everything.
--
--   This is the cohomological core of local class field theory for the layer $K_w/E_v$: vanishing of $H^1$ (Hilbert 90), the order of $H^2$, and generation of $H^2$ by the restriction of the local fundamental class. It supplies the hypothesis package used downstream for the norm/Tate–Nakayama statements at a finite place and for the explicit cochain description of the class, and enters the treatment of the global fundamental class through the local coordinates of the idèle class module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_fundamentalClass_units_adicCompletion
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ u : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) 2,
      (∀ S : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w),
          CategoryTheory.Limits.IsZero (groupCohomology
            (Rep.res S.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) 1)) ∧
      (∀ (S : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)) [Fintype S],
          Nat.card (groupCohomology
            (Rep.res S.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) 2) =
            Fintype.card S) ∧
      (∀ S : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w),
          Submodule.span ℤ {(groupCohomology.map S.subtype
            (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom u} = ⊤) := by sorry
