-- Prove2me | Theorems.Thm_OAI_MainGap_limitRep_nonzero
-- name    : OAI.MainGap.limitRep_nonzero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:06:48.076954+00:00
-- url     : https://prove2.me/theorems/2788b68d-c9aa-46bc-9222-b29bfa873aa5
-- title:
--   The ultralimit GNS representation keeps elements that stay visible on the chosen vectors
-- statement:
--   Let $A$ be a unital C$^*$-algebra, ordered by its positive cone. Let $\iota$ be a set and $\omega$ an ultrafilter on $\iota$. A limit along $\omega$ is a limit along the filter $\omega$, and a property holds for $\omega$-almost every $i$ if the set of indices where it holds belongs to $\omega$. For each $i\in\iota$ let $H_i$ be a complex Hilbert space (inner product linear in the second variable), $\pi_i:A\to B(H_i)$ a unital $*$-homomorphism, and $\xi_i\in H_i$ a vector with $\|\xi_i\|\le1$.
--
--   The vector functionals $\varphi_i(a)=\langle\xi_i,\pi_i(a)\xi_i\rangle$ are positive and satisfy $|\varphi_i(a)|\le\|a\|$. For each $a\in A$ the bounded family $(\varphi_i(a))_{i}$ therefore has a unique limit along $\omega$, and
--   $$\varphi_\omega(a)=\lim_{i\to\omega}\varphi_i(a)$$
--   is again a positive linear functional, that is, $\mathbb{C}$-linear with $\varphi_\omega(x)\ge0$ for $x\ge0$. The *limit representation* $\pi_\omega:A\to B(H_\omega)$ is the GNS representation of $\varphi_\omega$. Here $H_\omega$ is the Hilbert-space completion of $A$ for the semi-inner product $\langle x,y\rangle=\varphi_\omega(x^*y)$, with vectors of seminorm zero identified with $0$, and $\pi_\omega(a)[x]=[ax]$.
--
--   **Theorem.** Let $a\in A$ and $\delta>0$, and suppose that $\|\pi_i(a)\,\xi_i\|\ge\delta$ for $\omega$-almost every $i$, that is, $\{\,i\in\iota:\ \|\pi_i(a)\xi_i\|\ge\delta\,\}\in\omega$. Then
--   $$\pi_\omega(a)\neq0 .$$
--
--   This is the non-vanishing half of the behaviour of the limit representation: an element that moves the vectors $\xi_i$ by a uniformly positive amount survives in $\pi_\omega$. Combined with the fact that $\pi_\omega$ kills elements whose norms $\|\pi_i(\cdot)\|$ tend to $0$ along $\omega$, it allows separating elements by a single representation.
--
--   **Formalization Note** $\varphi_\omega$ and $\pi_\omega$ are `limitFunctional ω π ξ hξ` and `limitRep ω π ξ hξ`. The ultralimit of each bounded family is chosen by compactness of a closed disc in $\mathbb{C}$, and $\pi_\omega$ is Mathlib's unital GNS representation `gnsStarAlgHom`. The order on $A$ is any partial order making $A$ a star-ordered ring, hence the positive-cone order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Representation.lean#L174-L187

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

theorem OAI.MainGap.limitRep_nonzero (a : A) {δ : ℝ} (hδ : 0 < δ)
    (ha : ∀ᶠ i in (ω : Filter ι), δ ≤ ‖π i a (ξ i)‖) :
    limitRep ω π ξ hξ a ≠ 0 := by sorry
