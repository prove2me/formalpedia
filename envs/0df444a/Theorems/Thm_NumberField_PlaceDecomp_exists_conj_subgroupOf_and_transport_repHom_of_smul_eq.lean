-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
-- name    : NumberField.PlaceDecomp.exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/778418d5-ba22-5a59-ace9-0de545ce0138
-- title:
--   Conjugation transport of local unit representations along g w₁ = w
-- statement:
--   Let $E$ and $F$ be fields with $F$ a number field and $F$ an $E$-algebra, let $H$ be a subgroup of $G = F \simeq_{\mathrm{alg}[E]} F$, let $w, w_1$ be height-one primes of $\mathcal{O}_F$, and let $g \in G$ satisfy $g \bullet w_1 = w$. Write $D_v$ for [`NumberField.PlaceDecomp.decomp E F v`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of $G$ attached to the valuation subring of the $v$-adic valuation of $F$, and let $K \le D_w$ be the subgroup $(\mathrm{conj}_g H) \cap D_w$, realised as `(MulAut.conj g • H).subgroupOf (decomp E F w)`. The assertion is twofold: first, $K$ and $H \cap D_{w_1}$ have the same cardinality; second, there exist a monoid homomorphism $c'' : K \to H \cap D_{w_1}$ and a morphism $T''$ of representations from the restriction along $c''$ of the restriction along the inclusion $H \cap D_{w_1} \le D_{w_1}$ of the $D_{w_1}$-representation $\mathrm{Additive}\,(F_{w_1})^\times$ (the multiplicative action of the decomposition group on the units of the $w_1$-adic completion) to the restriction along the inclusion $K \le D_w$ of the analogous $D_w$-representation $\mathrm{Additive}\,(F_w)^\times$, such that $c''$ is bijective, $c''(x) = g^{-1} x g$ in $G$ for all $x \in K$, and $T''$ is, on units, the transport isomorphism $F_{w_1} \to F_w$ induced by $g$ and the equality $g \bullet w_1 = w$.
--
--   This is the local ingredient of the double-coset (Mackey) comparison for decomposition subgroups: conjugation by $g$ identifies $H \cap D_{w_1}$ with $(\mathrm{conj}_g H) \cap D_w$ compatibly with the induced isomorphism of the unit groups of the two completions. It is used in the Herbrand-quotient bookkeeping, where the sums over places of terms indexed by decomposition subgroups are compared with sums indexed by the intersections $H \cap D_w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport
open scoped Pointwise

theorem NumberField.PlaceDecomp.exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (H : Subgroup (F ≃ₐ[E] F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (g : F ≃ₐ[E] F) (hg : g • w₁ = w) :
    Nat.card ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) = Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) ∧
    ∃ (c'' : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)))
      (T'' : Rep.res c'' (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)) ⟶
        Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)),
      Function.Bijective c'' ∧
      (∀ x : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)),
        ((c'' x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁))) : F ≃ₐ[E] F) = g⁻¹ * ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) * g) ∧
      (∀ x : (w₁.adicCompletion F)ˣ, ((Additive.toMul (T''.hom (Additive.ofMul x)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
        NumberField.PlaceTransport.transport g hg (x : w₁.adicCompletion F)) := by sorry
