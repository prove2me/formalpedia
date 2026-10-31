-- Prove2me | Theorems.Thm_LearnManip_lemma_EC_3
-- name    : LearnManip.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:04.726977+00:00
-- url     : https://prove2.me/theorems/1493dabb-2373-461c-9964-2545c128f6d8
-- title:
--   Lemma EC.3, p.ec9 — separability; optimality over policies is clause (E) of the goal
-- statement:
--   Let $g$ be measurable with $|g(s,c)|\le A(1+s)$ and solve (EC.15),
--   $$g(s,c)=\sup_{q\ge0}\Bigl\{-cq+\alpha g\bigl(\tfrac{s}{1+sq},c\eta\bigr)+\frac{\sigma^2_{\mu^q}}{2\gamma(1-\alpha)^2}\Bigr\}.$$
--   Then $\mu/(1-\alpha)+g(s,c)$ solves the BDP equation (10). For every state and quantity, the objective of (13) at $q$ equals $\mu/(1-\alpha)$ plus the objective of (EC.15) at $q$, so the two problems have the same maximizers. Every solution of (10) in the growth class equals this separable function, which is (EC.14).
--
--   The optimality of $q^*$ over policies, the last sentence of the lemma, is clause (E) of the goal theorem.
--
--   Differences from the source:
--   - reading: G recursively defined as the solution of (EC.15) → any g in the growth class solving (EC.15); reason: the recursion has several solutions outside the class; existence is the milestone Theorem 1
--   - reading: max in (EC.15) → a least upper bound; reason: at c = 0 the supremum is not attained
--   - encoding: a distortion rule Λ ∈ D_{µ^q} → the distorted law G ≪ N(µ, σ²_{µ^q}) with y G-integrable, and the cost γ KL(G‖N); reason: (4) is a bijection Λ ↔ P^Λ with Λ = dP^Λ/dP, and E[Λ log Λ] is the relative entropy
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma EC.3, p.ec9 (PDF 48)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_IsBDPSolution
import Definitions.Def_LearnManip_dissemObjective
import Definitions.Def_LearnManip_manipObjective
import Definitions.Def_LearnManip_IsManipValue
import Definitions.Def_LearnManip_GClass
import Definitions.Def_LearnManip_InClass
import Definitions.Def_LearnManip_sepValue

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Lemma EC.3, p.ec9 (PDF 48), of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04): if `g` in the growth
class solves (EC.15), then `μ/(1−α) + g` solves the BDP equation; the objective of (13) at `q` is
`μ/(1−α)` plus the objective of (EC.15) at `q`, so the two have the same maximizers; and every solution
of the BDP equation in `InClass` is this separable function (EC.14).

**Formalization Note.** The optimality of `q*` over policies is clause (E) of `theorem_2`. -/
theorem lemma_EC_3 (P : Params) {g : ℝ≥0 → ℝ≥0 → ℝ} (hg : GClass g) (hm : IsManipValue P g) :
    IsBDPSolution P (sepValue P g) ∧
    (∀ (μ : ℝ) (s c q : ℝ≥0),
      dissemObjective P (sepValue P g) μ s c q = μ / (1 - (P.α : ℝ)) + manipObjective P g s c q) ∧
    ∀ w : ℝ → ℝ≥0 → ℝ≥0 → ℝ, InClass P w → IsBDPSolution P w →
      ∀ (μ : ℝ) (s c : ℝ≥0), w μ s c = sepValue P g μ s c := by sorry

end LearnManip
