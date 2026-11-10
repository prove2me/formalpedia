-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_lemma_8_1
-- name    : GeoLipLearn.Agnostic.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:53:19.591728+00:00
-- url     : https://prove2.me/theorems/cf38a16f-e540-4e07-ad4a-469f78aebc36
-- title:
--   Lemma 8.1 (Centering by a sample median)
-- statement:
--   Let $y$ have probability law $\mu$, finite second moment, mean $c$ and variance at most $V^2$, where $V\ge1$. Let $0<\delta<1/2$ and take an odd independent preliminary sample of $N\ge8\log(2/\delta)$ labels. Its median $m$ satisfies
--   $$\Pr[|m-c|\le2V]\ge1-\delta/2.$$
--   For every fixed real $m$ with $|m-c|\le2V$, a fresh label of law $\mu$ satisfies $\|y-m\|_2\le3V$. This separates the preliminary-sample event from the fresh-label moment bound.
--
--   Differences from the source:
--   - encoding: a real random variable, independent preliminary sample and a fresh label → its probability law μ, the finite product μ^N, and an L² norm under μ for each fixed m; reason: a law determines all three quantities and a fresh independent label has this same conditional law; finite second moment is the meaning of finite variance
--   - encoding: with probability at least 1 − δ → a measurable subset of the specified product probability space, of measure at least ENNReal.ofReal (1 − δ), on which all conclusions hold; reason: this records an actual measurable success event rather than using outer measure of an arbitrary set
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 32, Lemma 8.1

import Definitions.Def_GeoLipLearn_Agnostic_Corrector

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem lemma_8_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (V δ : ℝ) (hV : 1 ≤ V) (hvar : variance id μ ≤ V^2)
    (hδ : 0 < δ ∧ δ < 1/2) (N : ℕ) (hodd : Odd N)
    (hN : 8*Real.log (2/δ) ≤ (N : ℝ)) :
    HighProbability (Measure.pi fun _ : Fin N => μ) (δ/2)
      (fun u => |sampleMedian u - ∫ y, y ∂μ| ≤ 2*V) ∧
    ∀ m : ℝ, |m - ∫ y, y ∂μ| ≤ 2*V →
      eLpNorm (fun y => y-m) 2 μ ≤ ENNReal.ofReal (3*V) := by sorry

end GeoLipLearn.Agnostic
