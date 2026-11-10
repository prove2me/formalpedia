-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_8
-- name    : GEPPGrowth.Main.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:37:54.390472+00:00
-- url     : https://prove2.me/theorems/9ca2d095-555d-4e25-8971-d371090a02ac
-- title:
--   Lemma 4.8 — All real chi-square moments
-- statement:
--   Let $x\sim\chi^2_k$. Then, for every $m>-\dfrac{k}{2}$,
--
--   $$
--   \mathbb E[x^m]=2^m\dfrac{\Gamma(m+\frac{k}{2})}{\Gamma(\frac{k}{2})}
--   $$.
--
--   This supplies both positive and negative real chi-square moments.
--
--   Differences from the source:
--   - encoding: finite real moment E[x^m] for m>-k/2 → integrability and the Bochner integral of Real.rpow x m under the chi-square pushforward law; reason: makes the source finite expectation explicit, including every positive and negative real exponent
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.8, printed p.9, PDF p.10

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.8, printed p.9 / PDF p.10. Includes all real exponents in the printed domain and asserts integrability to avoid a junk Bochner value. -/
theorem lemma_4_8 (k : ℕ) (hk : 0 < k) (m : ℝ) (hm : -(k:ℝ)/2 < m) :
    Integrable (fun x : ℝ => Real.rpow x m) (chiSquare k) ∧
    (∫ x : ℝ, Real.rpow x m ∂(chiSquare k)) =
      Real.rpow 2 m * Real.Gamma (m + (k:ℝ)/2) / Real.Gamma ((k:ℝ)/2) := by sorry

end GEPPGrowth.Main
