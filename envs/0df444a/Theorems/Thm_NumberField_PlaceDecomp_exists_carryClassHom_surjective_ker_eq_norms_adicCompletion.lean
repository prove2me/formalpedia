-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
-- name    : NumberField.PlaceDecomp.exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/77ed2718-04f4-51cc-8f76-a7b70db2e8eb
-- title:
--   Local norm index via carry classes in H²(D_w, F_w^×)
-- statement:
--   Let $E$ and $F$ be number fields with $F$ a Galois extension of $E$, let $v$ be a nonzero prime of $\mathcal{O}_E$ and $w$ a nonzero prime of $\mathcal{O}_F$ lying over it, i.e. `w.under (𝓞 E) = v`. Write $D_w$ for [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation inside $F \simeq_{\mathrm{alg}[E]} F$, and let $(w.adicCompletion F)^\times$ carry its $D_w$-action, viewed through `Rep.ofMulDistribMulAction` as a $\mathbb{Z}$-linear representation $A$ of $D_w$. Assume given $t \in D_w$ such that every element of $D_w$ lies in the subgroup of integer powers of $t$, and that $t$ has finite order. Then there is a monoid homomorphism $\Psi$ from $(v.adicCompletion E)^\times$ to the multiplicative group underlying $\mathrm{H}^2(D_w, A)$ with the following four properties. First, for every unit $a$ of the $v$-adic completion of $E$, writing $\iota a$ for the image of $a$ under the unit map induced by the semialgebra homomorphism `adicCompletionSemialgHom` from $E_v$ to $F_w$, and for every witness that the carry function $(g,h) \mapsto \iota a$ if $\mathrm{ord}(t) \le \ell(g) + \ell(h)$ and $0$ otherwise — where $\ell$ is the representative exponent in $\{0,\dots,\mathrm{ord}(t)-1\}$ writing an element as a power of $t$ — is a $2$-cocycle, $\Psi a$ is the cohomology class of that cocycle under `H2π`. Second, $\Psi$ is surjective. Third, $\Psi a = 1$ if and only if there is a unit $b$ of $F_w$ whose finite product $\prod_{\sigma \in D_w} \sigma \cdot b$ equals, as an element of $F_w$, the image of $a$ under `adicCompletionSemialgHom`. Fourth, $\mathrm{H}^2(D_w, A)$ and $D_w$ have the same cardinality.
--
--   This is the local layer of class field theory for a cyclic decomposition group, in the form of Tate's isomorphism $\hat{H}^0 \cong H^2$ realised by explicit carry cocycles: it identifies $E_v^\times$ modulo local norms from $F_w^\times$ with $H^2(D_w, F_w^\times)$, a group of order $|D_w|$. It is used in the idelic computations of the Artin map and Herbrand-quotient arguments, being cited by the statements on the image of the idèles trivial at a place and on the existence of local elements generating the decomposition group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain
open groupCohomology
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)

    (t : ↥(NumberField.PlaceDecomp.decomp E F w))
    (ht : ∀ g : ↥(NumberField.PlaceDecomp.decomp E F w), g ∈ Subgroup.zpowers t) (hfin : IsOfFinOrder t) :
    ∃ Ψ : (v.adicCompletion E)ˣ →*
        Multiplicative (groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)),

      (∀ (a : (v.adicCompletion E)ˣ)
         (hc : carryFun (A := Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) t ht hfin
            (Additive.ofMul (Units.map
              (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
                v.adicCompletion E →* w.adicCompletion F) a)) ∈
            groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)),
         Ψ a = Multiplicative.ofAdd
           ((groupCohomology.H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom
             ⟨carryFun (A := Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) t ht hfin
               (Additive.ofMul (Units.map
                 (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
                   v.adicCompletion E →* w.adicCompletion F) a)), hc⟩)) ∧

      Function.Surjective Ψ ∧

      (∀ a : (v.adicCompletion E)ˣ, Ψ a = 1 ↔
         ∃ b : (w.adicCompletion F)ˣ,
           (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
             IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) (a : v.adicCompletion E)) ∧

      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) =
        Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by sorry
