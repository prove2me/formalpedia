-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/8f9a538c-de09-5ba7-bf4d-71daa1815fb2
-- title:
--   Rigidity lemma: contraction spreads to an open neighbourhood
-- statement:
--   Let $S$ be a commutative ring, and let $A$ and $Y$ be schemes with a morphism $f : A \to \operatorname{Spec} S$ satisfying the bundle of properties `AbelianSchemePropertyBundle`, i.e. $f$ is smooth, proper, each fibre $f^{-1}(\{s\})$ (as a subset of the underlying space) is connected and nonempty, and $f$ carries a relative group law: a group structure on the set of $S$-morphisms $T \to A$ for every $S$-scheme $t : T \to \operatorname{Spec} S$, natural in $T$. Let $g : Y \to \operatorname{Spec} S$ be a morphism, $\tau : A \to Y$ a morphism over $S$ (i.e. $g \circ \tau = f$), $c$ a section of $g$, and $e$ a section of $f$ with $\tau \circ e = c$. Let $s$ be a point of $\operatorname{Spec} S$, and suppose that for every algebraically closed field $K$ and every morphism $x : \operatorname{Spec} K \to A$ whose induced point $f(x(\mathfrak{m}_K))$, the image under $f$ of the image of the closed point, equals $s$, one has $\tau \circ x = c \circ f \circ x$. Then there is an open subset $U$ of $\operatorname{Spec} S$ containing $s$ such that $\tau \circ x = c \circ f \circ x$ for every algebraically closed field $K$ and every $x : \operatorname{Spec} K \to A$ with $f(x(\mathfrak{m}_K)) \in U$.
--
--   This is the open-locus form of the rigidity lemma for abelian schemes: a morphism out of $A$ that contracts the geometric points of one fibre onto the given section $c$ contracts the geometric points of all fibres over some open neighbourhood of $s$. It feeds the statement `eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain`, which promotes such pointwise contraction statements to an identity of morphisms over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
    {S : Type} [CommRing S] {A Y : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f)
    (g : Y ⟶ Spec (CommRingCat.of S)) (τ : A ⟶ Y) (hτ : τ ≫ g = f)
    (c : Spec (CommRingCat.of S) ⟶ Y) (hc : c ≫ g = 𝟙 _)
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _) (heτ : e ≫ τ = c)
    (s : ↥(Spec (CommRingCat.of S)))
    (hs : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
      f.base (x.base (IsLocalRing.closedPoint K)) = s → x ≫ τ = x ≫ f ≫ c) :
    ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
        f.base (x.base (IsLocalRing.closedPoint K)) ∈ U → x ≫ τ = x ≫ f ≫ c := by sorry
