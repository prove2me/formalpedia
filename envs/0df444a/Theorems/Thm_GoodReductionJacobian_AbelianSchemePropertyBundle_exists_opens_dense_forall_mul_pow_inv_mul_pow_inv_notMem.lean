-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_dense_forall_mul_pow_inv_mul_pow_inv_notMem
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_opens_dense_forall_mul_pow_inv_mul_pow_inv_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3eb2c7fb-b3f9-5b07-bd9e-32ee8c49c455
-- title:
--   Dense open locus where b x^{-j}u⁻ᶜ avoids a closed set
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$: an assignment, to every $k$-scheme $t : T \to \operatorname{Spec} k$, of a multiplication, unit and inversion on the set of $T$-points $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying the group axioms and compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative, i.e. its multiplication on $T$-points is commutative for every $t$, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, $f$ is proper, every fibre $f^{-1}(s)$ of the underlying map is connected, and a relative group law for $f$ exists. Let $Z$ be a closed subset of the underlying topological space of $A$, let $u_0$ be a section of $f$ (a $k$-point) whose value at the closed point of $\operatorname{Spec} k$ lies outside $Z$, let $b$ and $u$ be further sections of $f$, and let $j, c$ be natural numbers with $j \neq 0$. Then there is an open subscheme $U$ of $A$ whose underlying set is dense, such that for every section $x$ of $f$ whose value at the closed point of $\operatorname{Spec} k$ lies in $U$, the point $b \cdot (x^{j})^{-1} \cdot (u^{c})^{-1}$, formed in the group of sections of $f$ supplied by $L$, takes at the closed point of $\operatorname{Spec} k$ a value outside $Z$.
--
--   This is the generic-position statement that on an abelian variety over an algebraically closed field the $k$-points $x$ for which $b\,x^{-j}u^{-c}$ avoids a given proper closed subset form a dense open set; the hypothesis that $Z$ misses one $k$-point is what makes the locus non-empty. It is used in the construction of suitable translations and test points in the treatment of polarisations, being cited in the verification that certain line-bundle classes lie in a stabiliser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_dense_forall_mul_pow_inv_mul_pow_inv_notMem.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_opens_dense_forall_mul_pow_inv_mul_pow_inv_notMem
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (Z : Set ↥A) (hZ : IsClosed Z)
    (u₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hu₀ : u₀.1.base (IsLocalRing.closedPoint k) ∉ Z)
    (b u : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (j c : ℕ) (hj : j ≠ 0) :
    ∃ U : A.Opens, Dense (U : Set ↥A) ∧
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, x.1.base (IsLocalRing.closedPoint k) ∈ U →
        (letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); b * (x ^ j)⁻¹ * (u ^ c)⁻¹).1.base
          (IsLocalRing.closedPoint k) ∉ Z := by sorry
