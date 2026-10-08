-- Prove2me | Theorems.Thm_IDivGeom_ExpFam_lemma_3_1
-- name    : IDivGeom.ExpFam.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:18.158633+00:00
-- url     : https://prove2.me/theorems/b8b6fc20-3c99-4b55-aa55-5c7a7c84001b
-- title:
--   Lemma 3.1 — I(P_n‖Q) → 0 implies ∫ f dP_n → ∫ f dQ for f with an exponential moment
-- statement:
--   Let $Q$ and $P_1, P_2, \dots$ be probability distributions on $(X,\mathcal X)$, and let $f$ be a real-valued measurable function such that $e^{tf(x)}$ is $Q$-integrable for all sufficiently small $|t|$, i.e. for $|t|<\delta$ with some $\delta>0$. If
--   $$I(P_n\|Q)\to 0,$$
--   then $f$ is $P_n$-integrable for all large $n$, and
--   $$\int f\,dP_n\to\int f\,dQ.$$
--
--   The lemma upgrades convergence in I-divergence to convergence of the expectations of functions with exponential moments, which need not be bounded. In the proof of Theorem 3.3 it shows that the limit of a minimizing sequence still satisfies the moment constraints.
--
--   **Formalization Note** The first conclusion, $P_n$-integrability of $f$ for large $n$, is what makes $\int f\,dP_n$ a genuine integral (a Lean Bochner integral of a non-integrable function would be $0$); it is the reading of the page's "$\int f\,dP_n$" and not an additional claim. $\int f\,dQ$ is genuine because $f$ is $Q$-integrable under the exponential-moment hypothesis.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 157 (PDF 12), Lemma 3.1

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

theorem lemma_3_1 {X : Type*} [MeasurableSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (P : ℕ → Measure X) (hP : ∀ n, IsProbabilityMeasure (P n))
    (f : X → ℝ) (hf : Measurable f)
    (hexp : ∃ δ > 0, ∀ t : ℝ, |t| < δ → Integrable (fun x => Real.exp (t * f x)) Q)
    (hI : Tendsto (fun n => klDiv (P n) Q) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, Integrable f (P n)) ∧
      Tendsto (fun n => ∫ x, f x ∂(P n)) atTop (𝓝 (∫ x, f x ∂Q)) := by sorry

end IDivGeom.ExpFam
