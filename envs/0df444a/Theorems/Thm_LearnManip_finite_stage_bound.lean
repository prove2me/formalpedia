-- Prove2me | Theorems.Thm_LearnManip_finite_stage_bound
-- name    : LearnManip.finite_stage_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:43.562051+00:00
-- url     : https://prove2.me/theorems/23e1ec2b-8761-45ce-b838-16d637de8929
-- title:
--   Proof of Lemma EC.3, p.ec9 — $v=\lim_k v_k$, and every admissible policy earns at most $v_T$
-- statement:
--   For every state, the value iterates converge to the closed-form value,
--   $$\lim_{k\to\infty}v_k(\mu,s,c)=\frac{\mu}{1-\alpha}+G(s,c).$$
--   For every admissible policy $M$, however it depends on the history, and every horizon $T$,
--   $$J_T(M)\le\Bigl(\sum_{j<T}\alpha^j\Bigr)\mu_0+\hat G_T(s_0,c_1).$$
--
--   The bound is what makes the dynamic program the value of the sequential problem (8). It is the content of the printed appeal to standard results, and it needs no transversality condition: a policy may send the expected mean to $-\infty$.
--
--   Differences from the source:
--   - reading: by standard results, v is the limit of the k-stage values → the limit, and the bound of J_T(M) by v_T over all admissible policies; reason: the bound is the step the standard results stand for: the printed contraction argument is on bounded functions, which do not contain v
--   - encoding: expected discounted profit over T periods → partial sums in EReal of real payoffs minus extended nonnegative costs; reason: an infinite expected cost makes a period −∞, never free
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), proof of Lemma EC.3, p.ec9 (PDF 48)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_Policy
import Definitions.Def_LearnManip_IsAdmissible
import Definitions.Def_LearnManip_horizonValue
import Definitions.Def_LearnManip_vClosed
import Definitions.Def_LearnManip_geomSum
import Definitions.Def_LearnManip_hatG
import Definitions.Def_LearnManip_vk

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- The "standard results" of the proof of Lemma EC.3, p.ec9 (PDF 48), of Keppo, Kim, Zhang (SSRN
3465030, 2021-09-04): the value iterates converge, `v_k → v`, and every admissible, history-dependent
policy earns over `T` periods at most `v_T(μ₀, s₀, c₁) = (∑_{j<T} α^j) μ₀ + Ĝ_T(s₀, c₁)`.

**Formalization Note.** The second clause is what makes `v` the value of (8). It carries the supremum over
all policies, and it needs no transversality condition. -/
theorem finite_stage_bound (P : Params) :
    (∀ (μ : ℝ) (s c : ℝ≥0), Tendsto (fun k => vk P k μ s c) atTop (𝓝 (vClosed P μ s c))) ∧
    ∀ {s₀ : ℝ≥0} (M : Policy s₀) (μ₀ : ℝ) (c₁ : ℝ≥0), IsAdmissible M μ₀ → ∀ T : ℕ,
      horizonValue P M μ₀ c₁ T ≤ ((geomSum P T * μ₀ + hatG P T s₀ c₁ : ℝ) : EReal) := by sorry

end LearnManip
