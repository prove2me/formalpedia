-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_lemma_4_1
-- name    : GeoLipLearn.Agnostic.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:50.656374+00:00
-- url     : https://prove2.me/theorems/28ae6cd9-209b-4a24-a4be-35bf72525072
-- title:
--   Lemma 4.1 (Low-degree approximation with small squared defect)
-- statement:
--   Let $g:\mathbb R^d\to\mathbb R$ be globally 1-Lipschitz with $\|g\|_2\le B$. For $t>0$ and a natural degree bound $k$, set $Q=(U_tg)_{\le k}$. Then
--   $$\|Q\|_2\le B,\qquad \|Q-g\|_2\le\sqrt t+\frac{e^{-t(k+1)}}{\sqrt{k+1}},\qquad\Gamma(Q)\le e^{-2t(k+1)}.$$
--   This supplies the low-degree approximation with small squared gradient defect.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - encoding: ∥g∥₂ ≤ B → 0 ≤ B and normG 2 g ≤ ENNReal.ofReal B; reason: the source inequality already implies B≥0; the explicit sign prevents ofReal from collapsing a negative bound to zero
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 15, Lemma 4.1

import Definitions.Def_GeoLipLearn_Agnostic_Hermite

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem lemma_4_1 (d k : ℕ) (g : Space d → ℝ) (B t : ℝ)
    (hB0 : 0 ≤ B) (hg : LipschitzWith 1 g) (hB : normG 2 g ≤ ENNReal.ofReal B) (ht : 0 < t) :
    let Q := truncation k (ou t g)
    normG 2 Q ≤ ENNReal.ofReal B ∧
    normG 2 (Q-g) ≤ ENNReal.ofReal (Real.sqrt t + Real.exp (-t*(k+1))/Real.sqrt (k+1)) ∧
    defect Q ≤ Real.exp (-2*t*(k+1)) := by sorry

end GeoLipLearn.Agnostic
