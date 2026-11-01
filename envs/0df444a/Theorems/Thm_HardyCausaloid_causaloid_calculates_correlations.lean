-- Prove2me | Theorems.Thm_HardyCausaloid_causaloid_calculates_correlations
-- name    : HardyCausaloid.causaloid_calculates_correlations
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:51.618126+00:00
-- url     : https://prove2.me/theorems/537ceacf-d8a3-48e3-95ed-47b77e84cb14
-- title:
--   §4.5, (35)–(37) (corrected: the ratio is $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$): the causaloid decides and computes every conditional probability
-- statement:
--   Let $M$ be an experiment model and, for every location $x$, let $\Omega_x$ be a fiducial set of the elementary region $R_x$.
--
--   1. **Existence.** There is a causaloid $C$ of $M$ with elementary fiducial sets $\Omega_x$.
--   2. **Use.** For every causaloid $C$ of $M$, every pair of disjoint finite sets of locations $O_1,O_2$ with regions $R_1,R_2$, every label $\alpha_1$ of $R_1$ and every setting $F_2$ with outcome family $Y_2$ on $O_2$, write
--   $$\mathbf a=\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2),\qquad \mathbf b=\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2),$$
--   both computed from $C$ by the causaloid product, with $\beta_2$ over all outcome families under $F_2$. Then
--      1. both sums over $\beta_2$ (of vectors, and of probabilities under each preparation) are summable;
--      2. under every generalised preparation, the joint probability is $\mathbf a\cdot\mathbf p(R_1\cup R_2)$ and the probability of the conditioning event is $\mathbf b\cdot\mathbf p(R_1\cup R_2)$, so the ratio of (35) is $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$;
--      3. $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$ is well defined if and only if $\mathbf a$ is parallel to $\mathbf b$ (eq. (36));
--      4. every value $p$ satisfies $\mathbf a=p\,\mathbf b$ (eq. (37));
--      5. if $\mathbf b\neq0$, every value is $|\mathbf a|/|\mathbf b|$, the ratio of the Euclidean lengths;
--      6. $\mathbf b=0$ if and only if the conditioning event has probability $0$ under every generalised preparation.
--
--   This is the closing claim of §4.5: "if we know the causaloid we can calculate whether any probability is well defined and we can calculate its value if it is", for any pair of regions, which is the task set at the end of §3. Exchanging $O_1$ and $O_2$ gives the other conditional.
--
--   Differences from the source:
--   - correction: (35) p ≡ Prob(Y₁^{α₁} | Y₂^{α₂}, F₁^{α₁}, F₂^{α₂}) = r_{α₁α₂}·p / Σ_{β₂} r_{α₁β₂}·p → the ratio is condNum/condDen, the conditional Prob(Y₂ | Y₁, F₁, F₂) of eq. (7); reason: the printed left-hand side is false: with one setting at each of two locations, binary outcomes, Prob(0,0)=1/2, Prob(0,1)=1/4, Prob(1,0)=0, Prob(1,1)=1/4, Prob(Y₁=0 | Y₂=0) = 1 but the printed ratio is (1/2)/(3/4) = 2/3; the ratio with Σ over β₂ is the conditional of (7)
--   - reading: p is well defined: 'independent of the state p(R₁∪R₂)' (p.16) → CondWellDefined: some c equals condNum s / condDen s for every preparation s with condDen s ≠ 0; reason: the probability must not depend on the generalised preparation; preparations under which the conditioning event is impossible give no conditional probability
--   - reading: a is parallel to b, (36) → ∃ c : ℝ, a = c • b; reason: the form (37) writes; when b = 0 both sides of (36) hold
--   - reading: 'the ratio of the lengths of the vectors' → euclidLength a / euclidLength b, with euclidLength v = √(Σ_k v_k²); reason: length of a vector in ℝ^{Ω₁₂} is its Euclidean norm
--   - encoding: p equal to the ratio of the lengths (no condition stated) → the ratio clause is stated under b ≠ 0; reason: for b = 0 the ratio is 0/0, undefined; the condition excludes only that case
--   - generalization: (37) and the ratio of lengths → adds clause 2.6: b = 0 iff the conditioning event has probability 0 under every preparation; reason: states when the ratio clause applies; the other clauses are the page's claims
--   - reading: the causaloid Λ ≡ (subset of Λ's | RULES), (31), and 'once we have the causaloid' (p.16) → a causaloid is the list (30) of Λ matrices (Causaloid) with IsCausaloidOf C M; reason: (31) leaves RULES unspecified; every compressed form is used through the list (30) it reproduces, so the theorem covers it
--   - generalization: labels α₁ = 1, 2, … of (Y₁, F₁); sums over the outcomes β₂ → settings and outcomes of arbitrary types, unconditional sums (tsum/HasSum), summability proved in the conclusion; reason: the paper does not say the label sets are finite; finite label sets are the special case, where every tsum is a finite sum
--   - generalization: the causaloid built in §4.2–§4.4 from chosen fiducial sets → every causaloid C of M (any fiducial sets, any Λ matrices with IsCausaloidOf C M); reason: the conclusion holds for each of them, in particular for the one the paper builds
--   - reading: 'any pair of regions' (p.16), 'two disjoint regions' (p.12) → two disjoint finite sets O₁, O₂ of locations, regions R_{O₁}, R_{O₂}; reason: by (2) a region is a union of elementary regions R_x; §4.3 takes the regions disjoint
--   - encoding: a generalised preparation (Y_{R−R₁−R₂}, F_{R−R₁−R₂}) in R − R₁ − R₂ → a total label s whose values on the region are ignored (it enters only through glue); reason: the labels of R off the region are exactly the generalised preparations; same instances
--   - reading: a just sufficient set of probabilities (p.11), the fiducial set (p.12) → Fiducial: sufficient, and no proper subset is sufficient; reason: inclusion-minimality is the literal sense of just sufficient
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.5, eqs. (35)–(37) and the closing sentence, p.16; §3, p.9 and eq. (7), p.10

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid
import Definitions.Def_HardyCausaloid_Conditional

set_option autoImplicit false

namespace HardyCausaloid

/-- **The causaloid decides and computes every conditional probability**, Hardy, *Towards
Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure*,
arXiv:gr-qc/0608043v1, §4.5, eqs. (35)–(37) and the closing sentence, p.16 ("This works for any
pair of regions. Hence, if we know the causaloid we can calculate whether any probability is
well defined and we can calculate its value if it is").

For every model `M` and every family `Ω₁` of elementary fiducial sets:

1. (existence) there is a causaloid `C` of `M` with elementary fiducial sets `Ω₁`;
2. (use) for every causaloid `C` of `M`, every pair of disjoint finite sets of locations
   `O₁`, `O₂`, every label `α₁` of `R₁` and every setting `F₂` with outcome family `Y₂` on `O₂`,
   with `a = r_{α₁α₂}(R₁ ∪ R₂)` and `b = Σ_{β₂} r_{α₁β₂}(R₁ ∪ R₂)` computed from `C`:
   (a) both sums over `β₂` are summable; (b) the joint probability is `a · p(R₁ ∪ R₂)` and the
   probability of the conditioning event is `b · p(R₁ ∪ R₂)` (eq. (35), corrected);
   (c) `Prob(Y₂ | Y₁, F₁, F₂)` is well defined iff `a = c b` for some `c` (eq. (36));
   (d) every value `c` satisfies `a = c b` (eq. (37)); (e) if `b ≠ 0`, every value is
   `|a| / |b|`; (f) `b = 0` iff the conditioning event has probability `0` under every
   preparation. -/
theorem causaloid_calculates_correlations {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (Ω₁ : ∀ x, Finset (Label Setting Outcome x))
    (hΩ₁ : ∀ x, Fiducial (elemTable M x) (Ω₁ x)) :
    (∃ C : Causaloid Setting Outcome, C.Ω₁ = Ω₁ ∧ IsCausaloidOf C M) ∧
    ∀ C : Causaloid Setting Outcome, IsCausaloidOf C M →
    ∀ (O₁ O₂ : Finset X), Disjoint O₁ O₂ → ∀ (α₁ : Lab Setting Outcome O₁)
      (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)),
      (Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
          C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂))) ∧
        ∀ s, Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
          regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂)) s)) ∧
      (∀ s, condNum M α₁ F₂ Y₂ s = condA C α₁ F₂ Y₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s ∧
        condDen M α₁ F₂ s = condB C α₁ F₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) ∧
      (CondWellDefined M α₁ F₂ Y₂ ↔ ∃ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
      (∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c → condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
      (condB C α₁ F₂ ≠ 0 → ∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c →
        c = euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)) ∧
      (condB C α₁ F₂ = 0 ↔ ∀ s, condDen M α₁ F₂ s = 0) := by sorry

end HardyCausaloid
