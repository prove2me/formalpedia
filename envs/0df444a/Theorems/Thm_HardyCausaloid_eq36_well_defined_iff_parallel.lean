-- Prove2me | Theorems.Thm_HardyCausaloid_eq36_well_defined_iff_parallel
-- name    : HardyCausaloid.eq36_well_defined_iff_parallel
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:42.289243+00:00
-- url     : https://prove2.me/theorems/1074b309-d6a5-4a6e-9174-b5be575cc383
-- title:
--   Eq. (36) (corrected: $p=\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$): well defined iff $\mathbf r_{\alpha_1\alpha_2}\parallel\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}$
-- statement:
--   Let $C$ be a causaloid of the experiment model $M$, $O_1,O_2$ disjoint finite sets of locations with regions $R_1,R_2$, $\alpha_1$ a label of $R_1$, and $F_2$, $Y_2$ a setting and an outcome family on $O_2$. The conditional probability $p=\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$ is well defined — the ratio of the joint probability to the probability of the conditioning event takes one value under every generalised preparation where the latter is nonzero — if and only if
--   $$\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)\ \text{ is parallel to }\ \sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2)\qquad(36),$$
--   i.e. $\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)=c\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2)$ for some real $c$.
--
--   Both vectors are computed from the causaloid, so the causaloid decides whether any conditional probability between two regions is well defined, with no causal structure given in advance.
--
--   Differences from the source:
--   - correction: (35) p ≡ Prob(Y₁^{α₁} | Y₂^{α₂}, F₁^{α₁}, F₂^{α₂}) = r_{α₁α₂}·p / Σ_{β₂} r_{α₁β₂}·p → the ratio is condNum/condDen, the conditional Prob(Y₂ | Y₁, F₁, F₂) of eq. (7); reason: the printed left-hand side is false: with one setting at each of two locations, binary outcomes, Prob(0,0)=1/2, Prob(0,1)=1/4, Prob(1,0)=0, Prob(1,1)=1/4, Prob(Y₁=0 | Y₂=0) = 1 but the printed ratio is (1/2)/(3/4) = 2/3; the ratio with Σ over β₂ is the conditional of (7)
--   - reading: p is well defined: 'independent of the state p(R₁∪R₂)' (p.16) → CondWellDefined: some c equals condNum s / condDen s for every preparation s with condDen s ≠ 0; reason: the probability must not depend on the generalised preparation; preparations under which the conditioning event is impossible give no conditional probability
--   - reading: a is parallel to b, (36) → ∃ c : ℝ, a = c • b; reason: the form (37) writes; when b = 0 both sides of (36) hold
--   - generalization: labels α₁ = 1, 2, … of (Y₁, F₁); sums over the outcomes β₂ → settings and outcomes of arbitrary types, unconditional sums (tsum/HasSum), summability proved in the conclusion; reason: the paper does not say the label sets are finite; finite label sets are the special case, where every tsum is a finite sum
--   - generalization: the causaloid built in §4.2–§4.4 from chosen fiducial sets → every causaloid C of M (any fiducial sets, any Λ matrices with IsCausaloidOf C M); reason: the conclusion holds for each of them, in particular for the one the paper builds
--   - reading: 'any pair of regions' (p.16), 'two disjoint regions' (p.12) → two disjoint finite sets O₁, O₂ of locations, regions R_{O₁}, R_{O₂}; reason: by (2) a region is a union of elementary regions R_x; §4.3 takes the regions disjoint
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.5, eq. (36), p.16

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid
import Definitions.Def_HardyCausaloid_Conditional

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eq. (36): the conditional probability is well defined iff the two vectors are parallel**,
Hardy, arXiv:gr-qc/0608043v1, §4.5, eq. (36), p.16 ("1. p is well defined iff rα1α2(R1 ∪ R2) is
parallel to Σ_{β2} rα1β2(R1 ∪ R2)").

Let `C` be a causaloid of the model `M`, `O₁`, `O₂` disjoint, `α₁` a label of `R₁`, and `F₂`,
`Y₂` a setting and an outcome family on `O₂`. The conditional probability
`Prob(Y₂ | Y₁, F₁, F₂)` is well defined (the ratio of the joint probability to the probability
of the conditioning event takes one value `c` under every generalised preparation where the
denominator is nonzero) iff `r_{α₁α₂}(R₁ ∪ R₂) = c · Σ_{β₂} r_{α₁β₂}(R₁ ∪ R₂)` for some real `c`.
Both vectors are computed from `C` alone.

**Formalization Note** "Parallel" is `a = c • b` for a real `c`, the form of (37); when `b = 0`
both sides hold. -/
theorem eq36_well_defined_iff_parallel {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (C : Causaloid Setting Outcome) (hC : IsCausaloidOf C M)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) :
    CondWellDefined M α₁ F₂ Y₂ ↔ ∃ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂ := by sorry

end HardyCausaloid
