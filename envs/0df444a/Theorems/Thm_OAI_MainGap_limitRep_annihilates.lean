-- Prove2me | Theorems.Thm_OAI_MainGap_limitRep_annihilates
-- name    : OAI.MainGap.limitRep_annihilates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:04:23.352969+00:00
-- url     : https://prove2.me/theorems/6b35c8c2-5d36-4116-90e4-1fb2a35efd62
-- title:
--   The ultralimit GNS representation kills elements whose images become small
-- statement:
--   Let $A$ be a unital C$^*$-algebra, ordered by its positive cone. Let $\iota$ be a set and $\omega$ an ultrafilter on $\iota$. A limit along $\omega$ is a limit along the filter $\omega$, and a property holds for $\omega$-almost every $i$ if the set of indices where it holds belongs to $\omega$. For each $i\in\iota$ let $H_i$ be a complex Hilbert space (inner product linear in the second variable), $\pi_i:A\to B(H_i)$ a unital $*$-homomorphism, and $\xi_i\in H_i$ a vector with $\|\xi_i\|\le1$.
--
--   The vector functionals $\varphi_i(a)=\langle\xi_i,\pi_i(a)\xi_i\rangle$ are positive and satisfy $|\varphi_i(a)|\le\|a\|$. For each $a\in A$ the bounded family $(\varphi_i(a))_{i}$ therefore has a unique limit along $\omega$, and
--   $$\varphi_\omega(a)=\lim_{i\to\omega}\varphi_i(a)$$
--   is again a positive linear functional, that is, $\mathbb{C}$-linear with $\varphi_\omega(x)\ge0$ for $x\ge0$. The *limit representation* $\pi_\omega:A\to B(H_\omega)$ is the GNS representation of $\varphi_\omega$. Here $H_\omega$ is the Hilbert-space completion of $A$ for the semi-inner product $\langle x,y\rangle=\varphi_\omega(x^*y)$, with vectors of seminorm zero identified with $0$, and $\pi_\omega(a)[x]=[ax]$.
--
--   **Theorem.** Let $a\in A$. If the operator norms $\|\pi_i(a)\|$ tend to $0$ along $\omega$, then $a$ is annihilated by the limit representation:
--   $$\lim_{i\to\omega}\|\pi_i(a)\|=0\ \Longrightarrow\ \pi_\omega(a)=0 .$$
--
--   The limit representation combines the representations $\pi_i$, seen through the vectors $\xi_i$, into a single representation. This result shows that it kills every element that becomes negligible in the $\pi_i$. Together with the companion statement that $\pi_\omega(a)\neq0$ when $\|\pi_i(a)\xi_i\|$ stays above a positive constant for $\omega$-almost every $i$, it is used to build one representation that annihilates a prescribed set of elements while keeping another element visible.
--
--   **Formalization Note** $\varphi_\omega$ and $\pi_\omega$ are `limitFunctional ω π ξ hξ` and `limitRep ω π ξ hξ`. The ultralimit of each bounded family is chosen by compactness of a closed disc in $\mathbb{C}$, and $\pi_\omega$ is Mathlib's unital GNS representation `gnsStarAlgHom`. The order on $A$ is any partial order making $A$ a star-ordered ring, hence the positive-cone order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Representation.lean#L152-L172

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (ω : Ultrafilter ι) (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
  (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)

theorem OAI.MainGap.limitRep_annihilates (a : A)
    (ha : Tendsto (fun i => ‖π i a‖) (ω : Filter ι) (𝓝 0)) :
    limitRep ω π ξ hξ a = 0 := by sorry
