-- Prove2me | Theorems.Thm_HardyCausaloid_eq35_conditional_ratio
-- name    : HardyCausaloid.eq35_conditional_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:51.789984+00:00
-- url     : https://prove2.me/theorems/5ffc3368-7370-462f-b7bb-2e8c985e6472
-- title:
--   Eq. (35) (corrected: the ratio is $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$): the conditional as a ratio of two functionals of the state
-- statement:
--   Let $C$ be a causaloid of the experiment model $M$, $O_1,O_2$ disjoint finite sets of locations with regions $R_1,R_2$, $\alpha_1$ a label of $R_1$, and $F_2$, $Y_2$ a setting and an outcome family on $O_2$, so that $\alpha_2=(Y_2,F_2)$; $\beta_2$ runs over all outcome families under $F_2$. Then
--
--   1. the family $\beta_2\mapsto\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2)$ is summable in $\mathbb R^{\Omega_{12}}$, and for every generalised preparation the family $\beta_2\mapsto p_{\alpha_1\beta_2}$ is summable;
--   2. for every generalised preparation, with $\mathbf p=\mathbf p(R_1\cup R_2)$,
--   $$p_{\alpha_1\alpha_2}=\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)\cdot\mathbf p,\qquad \sum_{\beta_2}p_{\alpha_1\beta_2}=\Big(\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2)\Big)\cdot\mathbf p .$$
--
--   Hence the ratio of (35),
--   $$\frac{\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)\cdot\mathbf p(R_1\cup R_2)}{\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2)\cdot\mathbf p(R_1\cup R_2)},$$
--   is the joint probability divided by the probability of the conditioning event, i.e. $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$ under that preparation — the conditional probability of eq. (7). Both vectors are computed from the causaloid alone.
--
--   Differences from the source:
--   - correction: (35) p ≡ Prob(Y₁^{α₁} | Y₂^{α₂}, F₁^{α₁}, F₂^{α₂}) = r_{α₁α₂}·p / Σ_{β₂} r_{α₁β₂}·p → the ratio is condNum/condDen, the conditional Prob(Y₂ | Y₁, F₁, F₂) of eq. (7); reason: the printed left-hand side is false: with one setting at each of two locations, binary outcomes, Prob(0,0)=1/2, Prob(0,1)=1/4, Prob(1,0)=0, Prob(1,1)=1/4, Prob(Y₁=0 | Y₂=0) = 1 but the printed ratio is (1/2)/(3/4) = 2/3; the ratio with Σ over β₂ is the conditional of (7)
--   - generalization: labels α₁ = 1, 2, … of (Y₁, F₁); sums over the outcomes β₂ → settings and outcomes of arbitrary types, unconditional sums (tsum/HasSum), summability proved in the conclusion; reason: the paper does not say the label sets are finite; finite label sets are the special case, where every tsum is a finite sum
--   - generalization: the causaloid built in §4.2–§4.4 from chosen fiducial sets → every causaloid C of M (any fiducial sets, any Λ matrices with IsCausaloidOf C M); reason: the conclusion holds for each of them, in particular for the one the paper builds
--   - reading: 'any pair of regions' (p.16), 'two disjoint regions' (p.12) → two disjoint finite sets O₁, O₂ of locations, regions R_{O₁}, R_{O₂}; reason: by (2) a region is a union of elementary regions R_x; §4.3 takes the regions disjoint
--   - encoding: a generalised preparation (Y_{R−R₁−R₂}, F_{R−R₁−R₂}) in R − R₁ − R₂ → a total label s whose values on the region are ignored (it enters only through glue); reason: the labels of R off the region are exactly the generalised preparations; same instances
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.5, eq. (35), p.16

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid
import Definitions.Def_HardyCausaloid_Conditional

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eq. (35), corrected: the conditional probability as a ratio of two linear functionals of
the state**, Hardy, arXiv:gr-qc/0608043v1, §4.5, eq. (35), p.16 ("where β2 runs over all
outcomes for the measurement associated with α2 (recall that α2 labels a particular outcome of
a particular measurement)").

Let `C` be a causaloid of the model `M`, `O₁`, `O₂` disjoint finite sets of locations, `α₁` a
label of `R₁`, and `F₂`, `Y₂` a setting and an outcome family on `O₂`; `β₂` runs over all
outcome families under `F₂`. Then

1. the family `β₂ ↦ r_{α₁β₂}(R₁ ∪ R₂)` is summable in `ℝ^{Ω₁₂}`, and for every generalised
   preparation `s` the family of probabilities `β₂ ↦ p_{α₁β₂}(s)` is summable;
2. for every `s`, the joint probability is `r_{α₁α₂}(R₁ ∪ R₂) · p(R₁ ∪ R₂)` and the probability
   of the conditioning event is `(Σ_{β₂} r_{α₁β₂}(R₁ ∪ R₂)) · p(R₁ ∪ R₂)`.

So the ratio of (35) is `condNum s / condDen s`, which is `Prob(Y₂ | Y₁, F₁, F₂)` under the
preparation `s`, the probability of eq. (7) (p.10).

**Formalization Note** The printed left-hand side of (35), `Prob(Y₁ | Y₂, F₁, F₂)`, is not the
ratio (correction C1); Lean has no `Prob` symbol, and the conditional is the pair
`condNum`/`condDen`. -/
theorem eq35_conditional_ratio {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (C : Causaloid Setting Outcome) (hC : IsCausaloidOf C M)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) :
    Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
      C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂))) ∧
    (∀ s, Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
      regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂)) s)) ∧
    (∀ s, condNum M α₁ F₂ Y₂ s = condA C α₁ F₂ Y₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) ∧
    (∀ s, condDen M α₁ F₂ s = condB C α₁ F₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) := by sorry

end HardyCausaloid
