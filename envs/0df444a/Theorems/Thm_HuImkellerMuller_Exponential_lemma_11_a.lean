-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_lemma_11_a
-- name    : HuImkellerMuller.Exponential.lemma_11_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:08.785897+00:00
-- url     : https://prove2.me/theorems/80c2e121-d889-4b66-a3c1-ae03671396ca
-- title:
--   Lemma 11 (a), p. 12 — the process dist(a_t, C̃σ_t) is predictable
-- statement:
--   Let $(a_t)$ be an $\mathbb R^{1\times m}$-valued and $(\sigma_t)$ an $\mathbb R^{d\times m}$-valued predictable process, and let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed. Then the real process
--   $$\big(\operatorname{dist}(a_t,\tilde C\sigma_t)\big)_{t}$$
--   is predictable.
--
--   Together with part (b) this is the measurable-selection lemma that makes the driver $f$ of (7) a predictable random function and the optimal strategy a predictable process.
--
--   **Formalization Note** The page names this process $d$; the letter is not used since $d$ is the number of stocks. $\operatorname{dist}$ is `Metric.infDist`, the distance to the set $\tilde C\sigma_t$ (no closedness of the image is needed for the distance). The processes are indexed by $t\in\mathbb R_{\ge0}$.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, Lemma 11 (a), p. 12

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_Market

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- Lemma 11 (a), pp. 12–13: for predictable a and σ and a closed C̃, the process
dist(a_t, C̃σ_t) is predictable. -/
theorem lemma_11_a {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}
    (𝓕 : Filtration ℝ≥0 mΩ)
    (a : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (ha : IsPredictable 𝓕 a) (hσ : ∀ i j, IsPredictable 𝓕 (fun t ω => σ t ω i j))
    (Ct : Set (Fin d → ℝ)) (hCt : IsClosed Ct) :
    IsPredictable 𝓕 (fun t ω => Metric.infDist (a t ω) (Cset Ct σ t ω)) := by sorry

end HuImkellerMuller.Exponential
