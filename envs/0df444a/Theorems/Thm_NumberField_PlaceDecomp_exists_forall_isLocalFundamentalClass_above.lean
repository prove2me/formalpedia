-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_forall_isLocalFundamentalClass_above
-- name    : NumberField.PlaceDecomp.exists_forall_isLocalFundamentalClass_above
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/f5defbde-ec29-5419-8e1b-bdea028f7bfc
-- title:
--   Local fundamental classes above every finite place
-- statement:
--   Let $E$ and $F$ be number fields with $F/E$ Galois. The assertion is that one may choose, simultaneously for all $v$ in the height-one spectrum of $\mathcal{O}_E$: a prime number $q_v$; a subfield $L_v$ of a fixed algebraic closure $\mathbb{Q}_{q_v}^{\mathrm{alg}}$ of $\mathbb{Q}_{q_v}$, finite over $\mathbb{Q}_{q_v}$; actions of the group $D_v :=$ `decomp E F (above E F v)` — the decomposition subgroup inside $F \simeq_{\mathrm{alg}[E]} F$ of the valuation subring attached to the chosen prime `above E F v` of $\mathcal{O}_F$ over $v$ — on $L_v$ by semiring automorphisms and on $L_v^\times$ multiplicatively; a ring isomorphism $\Phi_v$ from the completion of $F$ at `above E F v` onto $L_v$; together with the compatibilities that $D_v$ fixes the image of $\mathbb{Q}_{q_v}$ in $L_v$, that the action on units is the restriction of that on $L_v$, and that $\Phi_v$ is $D_v$-equivariant; a subfield $K_{0,v} \subseteq \mathbb{Q}_{q_v}^{\mathrm{alg}}$ finite over $\mathbb{Q}_{q_v}$ which is a base for $(L_v, D_v)$, i.e. $K_{0,v} \le L_v$ and an element of $L_v$ lies in $K_{0,v}$ exactly when it is fixed by every element of $D_v$; a morphism $\theta_v$ of $\mathbb{Z}$-linear representations of $D_v$ from $L_v^\times$ to the units of the completion whose underlying map is $\Phi_v^{-1}$ on units; and a class $u_v \in H^2(D_v, L_v^\times)$ such that for every $v$ the class $u_v$ is a local fundamental class for $(q_v, L_v, D_v, K_{0,v})$: for every finite overlayer datum $(M, H, N_L, N_n, e, \varphi, \pi)$ over $L_v$ in the sense of [`ExtCitation.LocalLevel.IsUnramOverlayerDatum`](def/ExtCitation_LocalLevel_FundamentalClass.html#L18) and every units map $\iota$ lifting the inclusion $L_v \subseteq M$, the image of $u_v$ under the map induced by $e^{-1} \circ (\text{projection } H \to H/N_L)$ and $\iota$ equals the inflation from $H/N_n$ of the class of the carry $2$-cocycle attached to $\varphi$ and the uniformiser $\pi$.
--
--   This packages, at the chosen prime above each finite place of $E$, the local class field theory input for $F/E$: an equivariant identification of the local completion with a finite extension of $\mathbb{Q}_{q_v}$ inside a fixed algebraic closure, together with Tate's local fundamental class in $H^2$ of the decomposition group acting on the units. It is a bookkeeping step used in the descent of the reciprocity law from $p$-group layers to an arbitrary finite Galois layer, and is cited by the Herbrand-quotient computations of that descent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_forall_isLocalFundamentalClass_above.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_forall_isLocalFundamentalClass_above
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] :
    ∃ (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
      (L : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (L v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ)
      (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L v)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L v) y = algebraMap ℚ_[q v] (L v) y)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L v))ˣ), ((g • y : (↥(L v))ˣ) : L v) = g • (y : L v))
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
      (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
      (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
          (Φ v).symm (y : L v))
      (u : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ)),
      ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u v) := by sorry
