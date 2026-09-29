-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_forall_mem_of_isClosed_of_forall_torsion_mem
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.forall_mem_of_isClosed_of_forall_torsion_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/d9d53af0-e392-54c6-bd1e-e2fe0acde766
-- title:
--   ℓ-power torsion points are Zariski-dense in an abelian variety
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: a rule assigning to each $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ t^{-1}\text{-compatible, i.e. } t = f \circ \varphi\}$, satisfying associativity, the unit laws, left inversion, and naturality under base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$; assume $L$ is commutative ($hc$). Assume further the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $\ell$ be a prime that is nonzero in $k$. Let $Z$ be a closed subset of the space of $A$, and let $H$ be an additive subgroup of the group of $k$-points $L.AlgPoints$ (the $\operatorname{Spec} k$-sections of $f$ under $L$, written additively) such that a point $Q$ lies in $H$ precisely when the image of the closed point of $\operatorname{Spec} k$ under the underlying map of $Q$ lies in $Z$. If every $Q$ with $\ell^n \cdot Q = 0$ for some $n$ lies in $H$, then every $Q$ lies in $H$.
--
--   This is the Zariski-density of the $\ell$-power torsion subgroup $A[\ell^\infty](k)$ in an abelian variety $A$ over an algebraically closed field of characteristic different from $\ell$, stated in the form: a closed subset whose $k$-points form a subgroup containing all $\ell$-power torsion contains all $k$-points. It is used to produce line bundles and translations with prescribed behaviour on torsion, in the treatment of polarisations and Riemann forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_forall_mem_of_isClosed_of_forall_torsion_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.forall_mem_of_isClosed_of_forall_torsion_mem
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (Z : Set A) (hZ : IsClosed Z) (H : AddSubgroup (L.AlgPoints hc k))
    (hH : ∀ Q : L.AlgPoints hc k, Q ∈ H ↔ (RelativeGroupLaw.AlgPoints.toPoint Q).1.base (IsLocalRing.closedPoint k) ∈ Z)
    (htors : ∀ (n : ℕ) (Q : L.AlgPoints hc k), ℓ ^ n • Q = 0 → Q ∈ H)
    (Q : L.AlgPoints hc k) : Q ∈ H := by sorry
