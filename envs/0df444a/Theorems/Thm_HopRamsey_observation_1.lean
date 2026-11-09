-- Prove2me | Theorems.Thm_HopRamsey_observation_1
-- name    : HopRamsey.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:44:58.536385+00:00
-- url     : https://prove2.me/theorems/c9cafad6-e8f0-4f59-8f3f-ad9165ca0625
-- title:
--   Observation 1: $r_L=\Delta/4-\Delta/2^{L+4}<\Delta/4$
-- statement:
--   For the radii of Figure 2 with $L\ge1$ phases at scale $\Delta>0$, the largest radius is
--
--   $$
--   r_L=\frac\Delta4-\frac{\Delta}{2^{L+4}}<\frac\Delta4 .
--   $$
--
--   It bounds the radius of every ball carved by Algorithm 2 and gives, through Claim 1 and Corollary 1, the halving of the diameter at every level of the recursion.
--
--   Differences from the source:
--   - generalization: L = ⌈log log(|V|+1)⌉ and the scale ∆ of a call → every L ≥ 1 and every ∆ > 0; reason: the identity holds for every L ≥ 1; Figure 2's L is ≥ 1 when |V| ≥ 2
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Observation 1, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_HopRamsey_Fig2Params

open scoped ENNReal

namespace HopRamsey

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Observation 1, p.15 (PDF p.17): "r_L = ∆/4 − ∆/2^{L+4} < ∆/4."

**Formalization Note.** Stated for every number of phases `L ≥ 1` and every scale `∆ > 0`, with the
radii of Figure 2 (`radius L ∆ ℓ`); Figure 2's `L = ⌈log₂ log₂(|V|+1)⌉` is `≥ 1` when `|V| ≥ 2`. -/
theorem observation_1 (L : ℕ) (hL : 1 ≤ L) (Δ : ℝ) (hΔ : 0 < Δ) :
    radius L Δ L = Δ / 4 - Δ / 2 ^ (L + 4) ∧ radius L Δ L < Δ / 4 := by sorry

end HopRamsey
