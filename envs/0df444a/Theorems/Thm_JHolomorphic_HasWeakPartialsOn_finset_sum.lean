-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_finset_sum
-- name    : JHolomorphic.HasWeakPartialsOn.finset_sum
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:43:04.670114+00:00
-- url     : https://prove2.me/theorems/09da27d6-b9b9-4ec9-9b6b-a69caae8e701
-- title:
--   Weak partial derivatives of a finite sum
-- statement:
--   Let $U\subset\mathbb{C}$, let $E$ be a real normed space, let $s$ be a finite index set, and for each $i\in s$ let $u_i:\mathbb{C}\to E$ have weak partial derivatives $u_{i,s},u_{i,t}$ on $U$ (tested against real $C^\infty$ functions with compact support in $U$), with $u_i,u_{i,s},u_{i,t}$ integrable on every compact $K\subset U$. Then $\sum_{i\in s}u_i$ has weak partial derivatives $\sum_{i\in s}u_{i,s}$ and $\sum_{i\in s}u_{i,t}$ on $U$.
--
--   Finite sums of $W^{1,p}_{\mathrm{loc}}$-type maps arise when vector- or matrix-valued weak solutions are assembled from their components.
--
--   **Formalization Note** The index set is a `Finset ι`; weak partials are `JHolomorphic.HasWeakPartialsOn U _ _ _` from the imported setting and local integrability is `IntegrableOn _ K` for every compact `K ⊆ U`.
-- source:
--   Standard; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Weak partial derivatives of a finite sum: if each `uᵢ` has weak partials `uᵢₛ`, `uᵢₜ` on `U` and
`uᵢ, uᵢₛ, uᵢₜ` are integrable on every compact subset of `U`, then `∑ uᵢ` has weak partials `∑ uᵢₛ`,
`∑ uᵢₜ`. -/
theorem HasWeakPartialsOn.finset_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} (s : Finset ι) {u us ut : ι → ℂ → E}
    (h : ∀ i ∈ s, HasWeakPartialsOn U (u i) (us i) (ut i))
    (hint : ∀ i ∈ s, ∀ K ⊆ U, IsCompact K →
      IntegrableOn (u i) K ∧ IntegrableOn (us i) K ∧ IntegrableOn (ut i) K) :
    HasWeakPartialsOn U (fun z => ∑ i ∈ s, u i z) (fun z => ∑ i ∈ s, us i z)
      (fun z => ∑ i ∈ s, ut i z) := by
  sorry

end JHolomorphic
