-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_spec_glued_charts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/1163bf33-890c-5abb-8714-14b86a22d228
-- title:
--   Chart index map on A'-points: additive and surjective
-- statement:
--   Let $R$ and $A'$ be local rings and $\varphi_A : R \to A'$ a local homomorphism, and write $\sigma = \operatorname{Spec}(\varphi_A) : \operatorname{Spec} A' \to \operatorname{Spec} R$. Let $f : G \to \operatorname{Spec} R$ and $g_N : N \to \operatorname{Spec} R$ be morphisms of schemes carrying relative group laws $L$ and $L_N$ respectively, i.e. functorial multiplication, unit and inverse operations on the sets $\{\phi : T \to G \mid \phi \circ f = t\}$ (resp. for $g_N$) for every $t : T \to \operatorname{Spec} R$, satisfying associativity, unit and inverse laws and compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} R$. Let $\Phi$ be an additive abelian group and $e : \Phi \to (G \to N)$ a family of morphisms such that each $e_\varphi$ is an open immersion, each satisfies $e_\varphi$ followed by $g_N$ equals $f$, the union of the images of the underlying maps $|e_\varphi|$ is all of $N$, and for $\varphi \neq \psi$ every point of $N$ lying in both images has image under $|g_N|$ different from the closed point of $R$. Let $c : \Phi \times \Phi \to \{x : \operatorname{Spec} R \to G \mid x \circ f = \mathrm{id}\}$ be given, and assume the chart formula: for every $t : T \to \operatorname{Spec} R$, all $\varphi, \psi \in \Phi$ and all $a, b$ in the $L$-group of $T$-points of $G$ over $t$, the $L_N$-product of $a$ followed by $e_\varphi$ and $b$ followed by $e_\psi$ equals $L.\mathrm{mul}\,(L.\mathrm{mul}\,a\,b)\,(c_{\varphi\psi}$ pulled back along $t)$ followed by $e_{\varphi+\psi}$. Then there exists a map $\mathrm{spec}$ from the set of $s : \operatorname{Spec} A' \to N$ with $s$ followed by $g_N$ equal to $\sigma$ to $\Phi$ such that: $\mathrm{spec}(s) = \varphi$ holds if and only if $s$ factors as some $a : \operatorname{Spec} A' \to G$ over $\sigma$ followed by $e_\varphi$; $\mathrm{spec}$ is additive for the $L_N$-multiplication on these points; and $\mathrm{spec}$ is surjective.
--
--   This is the component-map construction for a group scheme presented as a union of translated copies of a fixed chart indexed by an abelian group $\Phi$: on points with values in a local ring receiving $R$ locally, the index of the unique chart through which a point factors is well defined and gives a surjective homomorphism onto $\Phi$. It is used in the construction of the Néron object attached to the Jacobian $J_0(N)$ at a prime, via [`ModularCurve.JZeroNeronObjectAtP.exists_neronGlue`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_neronGlue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_spec_glued_charts
    {R A' : Type u} [CommRing R] [IsLocalRing R] [CommRing A'] [IsLocalRing A']
    (φA : R →+* A') [IsLocalHom φA]
    {G N : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {gN : N ⟶ Spec (CommRingCat.of R)} (LN : RelativeGroupLaw R gN)
    {Φ : Type u} [AddCommGroup Φ]
    (e : Φ → (G ⟶ N)) (he : ∀ φ, IsOpenImmersion (e φ)) (hef : ∀ φ, e φ ≫ gN = f)
    (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    (hne : ∀ φ ψ, φ ≠ ψ → ∀ n ∈ Set.range (e φ).base ∩ Set.range (e ψ).base,
      gN.base n ≠ IsLocalRing.closedPoint R)
    (c : Φ → Φ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hchart : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ) (a b : SchemeHomOver s f),
        LN.mul s (NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩)
            (NeronModelInfra.schemeHomOverComp b ⟨e ψ, hef ψ⟩) =
          NeronModelInfra.schemeHomOverComp
            (L.mul s (L.mul s a b) (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) (c φ ψ)))
            ⟨e (φ + ψ), hef (φ + ψ)⟩) :
    ∃ spec : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN → Φ,
      (∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN) (φ : Φ),
        spec s = φ ↔ ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) f,
          NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩ = s) ∧
      (∀ s s' : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN,
        spec (LN.mul _ s s') = spec s + spec s') ∧
      Function.Surjective spec := by sorry
