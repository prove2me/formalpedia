-- Prove2me | Theorems.Thm_IntegerSumAmplification_Main_lemma_6_4
-- name    : IntegerSumAmplification.Main.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:02:39.114138+00:00
-- url     : https://prove2.me/theorems/80a09ebe-40aa-4824-8339-499e8dbceab3
-- title:
--   Lemma 6.4 — Averaged coordinate projections
-- statement:
--   Let $D$ be any probability law on a measurable space $W$, let $F:W^k\to\mathbb R$ be square-integrable under $D^k$, and let $I\subseteq\{1,\ldots,k\}$ be nonempty, with $r=|I|$. Define $g_i(w)$ by integrating $F$ over all coordinates except $i$, and $g_I=r^{-1}\sum_{i\in I}g_i$. Then
--   $$\mathbb E_D[g_I]=\mathbb E_{D^k}[F],\qquad
--   \operatorname{Var}_D(g_I)\le\frac{\operatorname{Var}_{D^k}(F)}r.$$
--   If, in addition, $0\le F\le1$, then $\operatorname{Var}_D(g_I)\le1/(4r)$. This is the general projection bound, with no finite-space or bounded-function restriction on the first two conclusions.
--
--   Differences from the source:
--   - encoding: independent samples from D → the product probability measure D^k; reason: integration and event measures give exactly the stated expectations and probabilities
--   - encoding: square-integrable F and sections defined almost everywhere → MemLp F 2 and Bochner section integrals; reason: MemLp supplies the measurability and integrability implicit in square integrability
--   - encoding: indices 1 through k → Fin k and a nonempty finite subset; reason: reindexing preserves every subset and its cardinality
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Lemma 6.4, printed p. 14 / PDF p. 17. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_CoordinateProjections
open MeasureTheory ProbabilityTheory

namespace IntegerSumAmplification.Main

theorem lemma_6_4 {W : Type*} [MeasurableSpace W] (D : Measure W)
    [IsProbabilityMeasure D] (k : ℕ) (F : (Fin k → W) → ℝ)
    (hF : MemLp F 2 (productLaw D k)) (I : Finset (Fin k)) (hI : I.Nonempty) :
    (∫ w, averagedProjection D F I w ∂D) = (∫ z, F z ∂productLaw D k) ∧
    variance (averagedProjection D F I) D ≤ variance F (productLaw D k) / I.card ∧
    ((∀ z, 0 ≤ F z ∧ F z ≤ 1) →
      variance (averagedProjection D F I) D ≤ 1 / (4 * (I.card : ℝ))) := by sorry

end IntegerSumAmplification.Main
