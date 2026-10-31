-- Prove2me | Theorems.Thm_LearnManip_corollary_1
-- name    : LearnManip.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:50.542835+00:00
-- url     : https://prove2.me/theorems/4c58ffb2-413a-46c2-ad42-62a8ceb39eea
-- title:
--   Corollary 1, p.13 (corrected: uniqueness in a growth class) — (10) and (13) are the same equation; value and policy are clauses (A), (E) of the goal
-- statement:
--   Let $w(\mu,s,c)$ be measurable with $|w(\mu,s,c)-\mu/(1-\alpha)|\le A(1+s)$. For every state and every $q\ge0$, the inner supremum of (10) over distortions at $q$ is attained, and it equals the objective of (13) at $q$,
--   $$-cq+\gamma\log E_{\mu,s}\Bigl[\exp\Bigl(\frac{\mu^q+\alpha w(\mu^q,\frac{s}{1+sq},c\eta)}{\gamma}\Bigr)\Bigr].$$
--   Consequently $w$ solves (10) iff it solves (13), the same $q$ are maximizers in both, and two solutions of (13) in this class coincide.
--
--   This reduces the problem to the optimization over quantities. The identification with the value function (8) and the optimality of $q^*$ are clauses (A) and (E) of the goal theorem.
--
--   Differences from the source:
--   - correction: the unique solution v of (13) → uniqueness among w with |w − µ/(1−α)| ≤ A(1+s); reason: same evidence as Lemma 1: no bounded solution, and v + c at α = 1/2, η = 2
--   - encoding: a distortion rule Λ ∈ D_{µ^q} → the distorted law G ≪ N(µ, σ²_{µ^q}) with y G-integrable, and the cost γ KL(G‖N); reason: (4) is a bijection Λ ↔ P^Λ with Λ = dP^Λ/dP, and E[Λ log Λ] is the relative entropy
--   - encoding: supremum over all Λ in (10) → pairs (q, G) of finite relative entropy, with IsLUB; reason: a distortion of infinite relative entropy has objective −∞, so excluding it changes no supremum
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Corollary 1, p.13, with (13); proof, pp.ec7–ec8 (PDF 46–47)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_baseLaw
import Definitions.Def_LearnManip_IsDistortion
import Definitions.Def_LearnManip_bdpObjective
import Definitions.Def_LearnManip_IsBDPSolution
import Definitions.Def_LearnManip_dissemObjective
import Definitions.Def_LearnManip_InClass

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Corollary 1, p.13, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), **corrected like Lemma 1**:
for `w` in the growth class `InClass`, the inner maximization of (10) at each `q` is attained and equals
the objective of (13); so `w` solves (10) iff it solves (13), the same `q` are maximizers, and a solution
of (13) in the class is unique.

**Formalization Note.** The identification of the solution with `V`, and the optimality of `q*`, are
clauses (A) and (E) of `theorem_2`. The growth class makes `e^{(…)/γ}` integrable under the normal law. -/
theorem corollary_1 (P : Params) {w : ℝ → ℝ≥0 → ℝ≥0 → ℝ} (hw : InClass P w) :
    (∀ (μ : ℝ) (s c q : ℝ≥0),
      IsGreatest {x : ℝ | ∃ G : Measure ℝ, IsDistortion μ s q G ∧
          klDiv G (baseLaw μ s q) ≠ ∞ ∧ x = bdpObjective P w μ s c q G}
        (dissemObjective P w μ s c q)) ∧
    (IsBDPSolution P w ↔ ∀ (μ : ℝ) (s c : ℝ≥0),
      IsLUB (Set.range (dissemObjective P w μ s c)) (w μ s c)) ∧
    (IsBDPSolution P w → ∀ (μ : ℝ) (s c q : ℝ≥0),
      (∃ G : Measure ℝ, IsDistortion μ s q G ∧ klDiv G (baseLaw μ s q) ≠ ∞ ∧
          bdpObjective P w μ s c q G = w μ s c) ↔
        dissemObjective P w μ s c q = w μ s c) ∧
    (∀ w' : ℝ → ℝ≥0 → ℝ≥0 → ℝ, InClass P w' →
      (∀ (μ : ℝ) (s c : ℝ≥0), IsLUB (Set.range (dissemObjective P w μ s c)) (w μ s c)) →
      (∀ (μ : ℝ) (s c : ℝ≥0), IsLUB (Set.range (dissemObjective P w' μ s c)) (w' μ s c)) →
      ∀ (μ : ℝ) (s c : ℝ≥0), w μ s c = w' μ s c) := by sorry

end LearnManip
