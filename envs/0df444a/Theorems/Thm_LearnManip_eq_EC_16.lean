-- Prove2me | Theorems.Thm_LearnManip_eq_EC_16
-- name    : LearnManip.eq_EC_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:00:25.328348+00:00
-- url     : https://prove2.me/theorems/8601b10e-678a-4851-b7b7-1640ce6cb1d1
-- title:
--   (EC.16), p.ec9 (corrected: upper index $k-1$) — the finite-stage decomposition
-- statement:
--   For every $k$ and every state,
--   $$v_k(\mu,s,c)=\Bigl(\sum_{j=0}^{k-1}\alpha^j\Bigr)\mu+\hat G_k(s,c),$$
--   where $v_k$ is the $k$-stage dynamic program and
--   $$\hat G_{k+1}(s,c)=\sup_{q\ge0}\Bigl\{-cq+\alpha\hat G_k\bigl(\tfrac{s}{1+sq},c\eta\bigr)+\frac{(\sum_{j=0}^{k}\alpha^j)^2\sigma^2_{\mu^q}}{2\gamma}\Bigr\},\qquad\hat G_0=0.$$
--   The suprema defining $v_{k+1}$ and $\hat G_{k+1}$ are genuine least upper bounds.
--
--   The decomposition is why the dynamic program is deterministic: the mean enters linearly, with a known coefficient, at each stage.
--
--   Differences from the source:
--   - correction: Σ_{j=0}^{k} α^j in (EC.16), and in the coefficient of Ĝ_k → Σ_{j=0}^{k−1} α^j; reason: the proof's own base case is v₁ = µ + Ĝ₁, while the printed sum at k = 1 gives (1 + α)µ
--   - reading: max → a least upper bound; reason: at c = 0 the supremum is not attained
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), proof of Lemma EC.3, (EC.16), p.ec9 (PDF 48)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_dissemObjective
import Definitions.Def_LearnManip_geomSum
import Definitions.Def_LearnManip_hatObjective
import Definitions.Def_LearnManip_hatG
import Definitions.Def_LearnManip_vk

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- (EC.16), proof of Lemma EC.3, p.ec9 (PDF 48), of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04),
**index corrected**: `v_k(μ, s, c) = (∑_{j<k} α^j) μ + Ĝ_k(s, c)`, the upper index being `k − 1`. The first
two clauses say that the `sSup`s in `hatG` and `vk` are genuine least upper bounds. -/
theorem eq_EC_16 (P : Params) :
    (∀ (k : ℕ) (s c : ℝ≥0),
      IsLUB (Set.range (hatObjective P k (hatG P k) s c)) (hatG P (k + 1) s c)) ∧
    (∀ (k : ℕ) (μ : ℝ) (s c : ℝ≥0),
      IsLUB (Set.range (dissemObjective P (vk P k) μ s c)) (vk P (k + 1) μ s c)) ∧
    ∀ (k : ℕ) (μ : ℝ) (s c : ℝ≥0), vk P k μ s c = geomSum P k * μ + hatG P k s c := by sorry

end LearnManip
