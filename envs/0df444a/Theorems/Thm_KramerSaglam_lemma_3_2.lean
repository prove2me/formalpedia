-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_2
-- name    : KramerSaglam.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:54.381573+00:00
-- url     : https://prove2.me/theorems/86d867e1-4b8b-4415-bae0-e2012ee34c86
-- title:
--   Lemma 3.2 — some coordinate has $\bar I(C\,;Y_i)\le 1/4$
-- statement:
--   In the model of Theorem 1.1, when $n\ge2$ there exists $i\in[n]$ such that
--   $$
--   \bar I(C\,;Y_i)\le\frac14 .
--   $$
--
--   This is the coordinate on which the induction step conditions.
--
--   Differences from the source:
--   - generalization: a bit C obtained from Y (deterministically in the abstract) → C obtained from Y through any g : {0,1}ⁿ → [0, 1]; reason: a deterministic bit is the case g = indicator, and the proof only uses 0 ≤ C ≤ 1
--   - encoding: the bit Y_i → the event {Y_i = 1} and its σ-algebra; reason: same information
--   - encoding: random variables X, Y, C of the model → measurable maps and an event on any probability space with the model's joint law, information through conditional expectations; reason: the quantities depend only on that law
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.2, p.4

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.2.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.4: when `n ≥ 2`, some coordinate satisfies `Ī(C ; Y_i) ≤ 1/4`. -/
theorem lemma_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n) (p : ℝ) (g : GeneralCK.Cube n → ℝ)
    (X Y : Ω → GeneralCK.Cube n) (C : Set Ω) (h : IsModel P p g X Y C) :
    ∃ i : Fin n, tsInfo P C (sigma (coordSet Y i)) ⊥ ≤ 1 / 4 := by sorry

end KramerSaglam
