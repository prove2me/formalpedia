-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmulPt_eq_of_isAlgClosed_of_isCommutative
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmulPt_eq_of_isAlgClosed_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/794901c8-5ac1-5433-a06f-b47450b814ee
-- title:
--   Divisibility of k-points of an abelian variety, k algebraically closed
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$ in the sense of the project's structure `RelativeGroupLaw`: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points over $t$, satisfying associativity, the two unit laws and left inverse cancellation, and compatible with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $L$ is commutative, i.e. the multiplication on $T$-points over $t$ is commutative for all $T$ and $t$, and assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, $f$ is proper, every fibre $f^{-1}(s)$ of the underlying map of topological spaces is connected, and $f$ admits at least one relative group law. Let $n$ be a nonzero natural number and let $Q$ be a morphism $\operatorname{Spec} k \to A$ whose composite with $f$ is the identity. Then there is a morphism $P : \operatorname{Spec} k \to A$ with composite $f$ equal to the identity such that the $n$-fold iterate $\mathrm{nsmulPt}$ of $L$ — defined by sending $0$ to the unit and $m+1$ to $\mathrm{nsmulPt}(m)$ multiplied by the point — applied to $P$ equals $Q$.
--
--   This is the classical statement that multiplication by $n \neq 0$ is surjective on the group of $k$-points of an abelian variety over an algebraically closed field, here in the form of the project's relative group laws on $\operatorname{Spec} k$-points. It is used in the study of polarisations and of kernels of isogenies, for instance in producing symmetric line bundles and in arguments where an $n$-divisible point is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmulPt_eq_of_isAlgClosed_of_isCommutative.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmulPt_eq_of_isAlgClosed_of_isCommutative
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hn : n ≠ 0) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      nsmulPt L (𝟙 (Spec (CommRingCat.of k))) n P = Q := by sorry
