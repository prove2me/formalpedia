-- Prove2me | Theorems.Thm_HardyCausaloid_eq37_value_ratio_of_lengths
-- name    : HardyCausaloid.eq37_value_ratio_of_lengths
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:39.82031+00:00
-- url     : https://prove2.me/theorems/1da8421b-53f4-44e3-b13e-1b1b3aba21f1
-- title:
--   Eq. (37) (corrected: $p=\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$): the value of $p$, and the ratio of lengths
-- statement:
--   Let $C$ be a causaloid of the experiment model $M$, $O_1,O_2$ disjoint finite sets of locations with regions $R_1,R_2$, $\alpha_1$ a label of $R_1$, and $F_2$, $Y_2$ a setting and an outcome family on $O_2$. Write $\mathbf a=\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)$ and $\mathbf b=\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2)$. Then
--
--   1. every value $p$ of $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$ satisfies
--   $$\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)=p\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2)\qquad(37);$$
--   2. if $\mathbf b\neq0$, every value is the ratio of the Euclidean lengths, $p=|\mathbf a|/|\mathbf b|$;
--   3. $\mathbf b=0$ if and only if the conditioning event has probability $0$ under every generalised preparation (and then every real number is a value, vacuously).
--
--   So when the conditional probability is well defined the causaloid also gives its value.
--
--   Differences from the source:
--   - correction: (35) p ≡ Prob(Y₁^{α₁} | Y₂^{α₂}, F₁^{α₁}, F₂^{α₂}) = r_{α₁α₂}·p / Σ_{β₂} r_{α₁β₂}·p → the ratio is condNum/condDen, the conditional Prob(Y₂ | Y₁, F₁, F₂) of eq. (7); reason: the printed left-hand side is false: with one setting at each of two locations, binary outcomes, Prob(0,0)=1/2, Prob(0,1)=1/4, Prob(1,0)=0, Prob(1,1)=1/4, Prob(Y₁=0 | Y₂=0) = 1 but the printed ratio is (1/2)/(3/4) = 2/3; the ratio with Σ over β₂ is the conditional of (7)
--   - reading: p is well defined: 'independent of the state p(R₁∪R₂)' (p.16) → CondWellDefined: some c equals condNum s / condDen s for every preparation s with condDen s ≠ 0; reason: the probability must not depend on the generalised preparation; preparations under which the conditioning event is impossible give no conditional probability
--   - reading: 'the ratio of the lengths of the vectors' → euclidLength a / euclidLength b, with euclidLength v = √(Σ_k v_k²); reason: length of a vector in ℝ^{Ω₁₂} is its Euclidean norm
--   - encoding: p equal to the ratio of the lengths (no condition stated) → the ratio clause is stated under b ≠ 0; reason: for b = 0 the ratio is 0/0, undefined; the condition excludes only that case
--   - generalization: (37) and the ratio of lengths → adds clause 3: b = 0 iff the conditioning event has probability 0 under every preparation; reason: states when the ratio clause applies; clauses 1–2 are the page's claims
--   - generalization: labels α₁ = 1, 2, … of (Y₁, F₁); sums over the outcomes β₂ → settings and outcomes of arbitrary types, unconditional sums (tsum/HasSum), summability proved in the conclusion; reason: the paper does not say the label sets are finite; finite label sets are the special case, where every tsum is a finite sum
--   - generalization: the causaloid built in §4.2–§4.4 from chosen fiducial sets → every causaloid C of M (any fiducial sets, any Λ matrices with IsCausaloidOf C M); reason: the conclusion holds for each of them, in particular for the one the paper builds
--   - reading: 'any pair of regions' (p.16), 'two disjoint regions' (p.12) → two disjoint finite sets O₁, O₂ of locations, regions R_{O₁}, R_{O₂}; reason: by (2) a region is a union of elementary regions R_x; §4.3 takes the regions disjoint
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.5, eq. (37), p.16

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid
import Definitions.Def_HardyCausaloid_Conditional

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eq. (37): the value of a well-defined conditional probability, as a ratio of lengths**,
Hardy, arXiv:gr-qc/0608043v1, §4.5, eq. (37), p.16 ("2. If p is well defined then it is given by
rα1α2(R1 ∪ R2) = p Σ_{β2} rα1β2(R1 ∪ R2) (i.e. equal to the ratio of the lengths of the
vectors).").

Let `C` be a causaloid of the model `M`, `O₁`, `O₂` disjoint, `α₁` a label of `R₁`, and `F₂`,
`Y₂` a setting and an outcome family on `O₂`; write `a = r_{α₁α₂}(R₁ ∪ R₂)` and
`b = Σ_{β₂} r_{α₁β₂}(R₁ ∪ R₂)`. Then

1. every value `c` of `Prob(Y₂ | Y₁, F₁, F₂)` satisfies `a = c b`;
2. if `b ≠ 0`, every value `c` is the ratio of the Euclidean lengths, `c = |a| / |b|`;
3. `b = 0` iff the conditioning event has probability `0` under every generalised preparation.
-/
theorem eq37_value_ratio_of_lengths {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (C : Causaloid Setting Outcome) (hC : IsCausaloidOf C M)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) :
    (∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c → condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
    (condB C α₁ F₂ ≠ 0 → ∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c →
      c = euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)) ∧
    (condB C α₁ F₂ = 0 ↔ ∀ s, condDen M α₁ F₂ s = 0) := by sorry

end HardyCausaloid
