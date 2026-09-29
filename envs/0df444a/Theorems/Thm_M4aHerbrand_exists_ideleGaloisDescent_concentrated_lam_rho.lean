-- Prove2me | Theorems.Thm_M4aHerbrand_exists_ideleGaloisDescent_concentrated_lam_rho
-- name    : M4aHerbrand.exists_ideleGaloisDescent_concentrated_lam_rho
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/357b71c8-635b-5ec9-b543-5ea4f28c49fd
-- title:
--   Existence of an idèle-class frame for a Galois layer
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, and write $G = F \simeq_{\mathrm{alg}[E]} F$ for its Galois group, $\mathbb{A}_F$ for the adèle ring of $F$ over $\mathcal{O}_F$, and $C_F = \mathbb{A}_F^\times / \mathrm{Im}(F^\times)$ for the quotient of the idèle group by the image of $F^\times$ under the unit map of $F \to \mathbb{A}_F$. The assertion is that the following data exist simultaneously. First, a descent datum $D$: a monoid homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_F$, each automorphism continuous, with $D.\mathrm{act}\,g$ restricting along $F \to \mathbb{A}_F$ to $g$. Second, a multiplicative-distributive action of $G$ on $C_F$ whose action map coincides with the map `D.classAct` induced by $D$ on the quotient. Third, for every height-one prime $w$ of $\mathcal{O}_F$ a homomorphism $\iota_w \colon (F_w)^\times \to \mathbb{A}_F^\times$ concentrated at $w$: its $w$-component `finPart w` is $x$, its component at every $w' \neq w$ is $1$, and its infinite part `infPart` is $1$. Fourth, for every such $w$, a morphism $\lambda_w$ of representations of the decomposition subgroup $D_w =$ `decomp E F w` (the decomposition subgroup over $E$ of the valuation subring of the $w$-adic valuation of $F$) from $(F_w)^\times$ to the restriction to $D_w$ of $C_F$, acting by $x \mapsto [\iota_w(x)]$; and a morphism $\rho_w$ of $D_w$-representations from the restriction to $D_w$ of $F^\times$ to $(F_w)^\times$, acting by $u \mapsto$ the image of $u$ under $F \to F_w$. Here all multiplicative groups are regarded as $G$- or $D_w$-modules via `Additive` and the morphisms are morphisms in `Rep`.
--
--   This supplies, for an arbitrary finite Galois layer of number fields, the package of idèle-theoretic data (Galois action on adèles and idèle classes, idèles concentrated at one finite place, and the local-to-global and coefficient maps equivariant for the decomposition group) on which the global invariant maps on idèle-class cohomology and the local–global compatibility of the fundamental class are predicated. It is used in the construction of the invariants attached to a $p$-group layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_ideleGaloisDescent_concentrated_lam_rho.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_ideleGaloisDescent_concentrated_lam_rho
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] :
    ∃ (D : IdeleGaloisDescent (𝓞 F) E F)
      (_ : MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
      (_ : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
      (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
      (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
        finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
      (lam : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
            (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
      (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
        (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
      (ρ : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ),
      ∀ (w : HeightOneSpectrum (𝓞 F)) (u : Fˣ),
        (ρ w).hom (Additive.ofMul u) =
          Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u) := by sorry
