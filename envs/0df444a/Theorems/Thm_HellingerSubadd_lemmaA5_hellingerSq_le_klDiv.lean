-- Prove2me | Theorems.Thm_HellingerSubadd_lemmaA5_hellingerSq_le_klDiv
-- name    : HellingerSubadd.lemmaA5_hellingerSq_le_klDiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:49:33.785981+00:00
-- url     : https://prove2.me/theorems/b4af96b0-bd98-4f92-96b0-fc96ce406799
-- title:
--   Lemma A.5 (second bullet): $D^2_{\mathrm H}(P,Q)\le D_{\mathrm{KL}}(P\|Q)$
-- statement:
--   Let $P$ and $Q$ be probability measures on a measurable space. Then
--
--   $$
--   D^2_{\mathrm H}(P,Q)\le D_{\mathrm{KL}}(P\,\|\,Q),
--   $$
--
--   where $D_{\mathrm{KL}}(P\|Q)=\int\log(dP/dQ)\,dP$ if $P\ll Q$ and $+\infty$ otherwise.
--
--   In the proof of Lemma A.13 this turns the squared Hellinger distances of Terms I and II into KL divergences, to which the chain rule applies.
--
--   Differences from the source:
--   - encoding: D_KL(P ∥ Q) as defined on p. 10, real or +∞ → Mathlib's klDiv μ ν : ℝ≥0∞, compared in ℝ≥0∞; reason: for probability measures klDiv equals the paper's definition (a non-integrable log-likelihood ratio has integral +∞)
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Lemma A.5, second bullet, p. 71

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory InformationTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Lemma A.5, second bullet: squared Hellinger distance is at most KL divergence.**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Lemma A.5, second bullet, p. 71: "D²_H(P, Q) ≤ D_KL(P ∥ Q)".

For probability measures `μ, ν` on one measurable space, `D²_H(μ, ν) ≤ D_KL(μ ∥ ν)`.

**Formalization Note.** KL divergence is Mathlib's `klDiv` (value `∞` off absolute continuity and
off integrability of the log-likelihood ratio; for probability measures this is the paper's
definition, p. 10). Both sides in `ℝ≥0∞`. -/
theorem lemmaA5_hellingerSq_le_klDiv {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    hellingerSq μ ν ≤ klDiv μ ν := by sorry

end HellingerSubadd
