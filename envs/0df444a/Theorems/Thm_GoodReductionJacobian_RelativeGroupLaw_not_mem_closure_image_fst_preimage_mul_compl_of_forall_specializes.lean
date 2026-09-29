-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
-- name    : GoodReductionJacobian.RelativeGroupLaw.not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/431cc366-e7af-5668-a6b0-cff885e97ad2
-- title:
--   Translation bad locus avoids maximal points of the special fibre
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain), let $B$ be a scheme and let $g\colon B \to \operatorname{Spec} R$ be smooth, separated and quasi-compact. Let `LB` be a relative group law for $g$: an assignment, to each scheme $T$ and each $t\colon T \to \operatorname{Spec} R$, of a multiplication, unit and inverse on the set of morphisms $\varphi\colon T \to B$ with $\varphi$ followed by $g$ equal to $t$, satisfying associativity, both unit laws and left inverse, and compatible with precomposition by any $\psi\colon T' \to T$ over $\operatorname{Spec} R$. Let $U$ be an open subset of $B$ containing every point $b$ that is maximal in its fibre, i.e. such that any $y$ with $y \rightsquigarrow b$ and $g(y) = g(b)$ equals $b$. Let $s_0 \in B$ be closed in its fibre: any $y$ with $s_0 \rightsquigarrow y$ and $g(y) = g(s_0)$ equals $s_0$. Let $\eta \in B$ lie over the closed point of $R$ and be maximal there: any $y$ with $y \rightsquigarrow \eta$ lying over the closed point equals $\eta$. Write $\sigma_0\colon \operatorname{Spec}\kappa(s_0) \to B$ for the canonical morphism `B.fromSpecResidueField s₀`, put $t_0 = \sigma_0$ followed by $g$, and form $P = B \times_{\operatorname{Spec} R} \operatorname{Spec}\kappa(s_0)$, regarded as a scheme over $\operatorname{Spec} R$ via the second projection followed by $t_0$. In the group of such sections over $P$, let $\rho$ be the product of the first projection (with the pullback square as its witness) and of the second projection followed by $\sigma_0$. The conclusion is that $\eta$ does not lie in the closure of the image under the first projection of the preimage, under the underlying continuous map of $\rho$, of the complement of $U$.
--
--   This is the topological step in Bosch–Lütkebohmert–Raynaud 6.4, Proposition 2: translating a fibrewise-dense open by a point closed in its fibre leaves a bad locus whose closure misses the maximal points of the special fibre. It feeds the construction of an open subgroup-law neighbourhood in [`GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem), and uses that the local ring of a smooth $R$-scheme at a point maximal in the special fibre is a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
      ((LB.mul (pullback.snd g (B.fromSpecResidueField s₀ ≫ g) ≫ (B.fromSpecResidueField s₀ ≫ g))
          ⟨pullback.fst g (B.fromSpecResidueField s₀ ≫ g), pullback.condition⟩
          (schemeHomOverComp (pullback.snd g (B.fromSpecResidueField s₀ ≫ g)) rfl
            (⟨B.fromSpecResidueField s₀, rfl⟩ :
              SchemeHomOver (B.fromSpecResidueField s₀ ≫ g) g))).1.base ⁻¹' ((U : Set B)ᶜ))) := by sorry
