-- Prove2me | Theorems.Thm_IntegerSumAmplification_Main_lemma_6_3
-- name    : IntegerSumAmplification.Main.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:03:19.275419+00:00
-- url     : https://prove2.me/theorems/5b554637-f715-4172-b8e6-7c814bd41074
-- title:
--   Lemma 6.3 — A common quantile for most pairs
-- statement:
--   Let $k>0$, let $D$ be any joint law on $\{0,1\}^n\times\{0,\ldots,m-1\}$, and let $A:U^k\to\mathbb Z$ succeed in predicting the sum of $k$ independent labels with probability at least $\varepsilon>0$. Define $p^-,p^+,\psi,b^-,b^+$ from the global residual and random restrictions. Then
--   $$\mathbb E[b^-]=p^-,\quad\mathbb E[b^+]=p^+,\qquad
--   \operatorname{Var}(b^-)\le\frac1{4k},\quad\operatorname{Var}(b^+)\le\frac1{4k}.$$
--   With probability at least $1-8/(k\varepsilon^2)$ over a fresh $(X,Y)\sim D$, both $|b^-(X,Y)-p^-|\le\varepsilon/4$ and $|b^+(X,Y)-p^+|\le\varepsilon/4$ hold. Every pair on that event satisfies
--   $$b^-(X,Y)\le\psi-\varepsilon/4,\qquad b^+(X,Y)\ge\psi+\varepsilon/4.$$
--   This keeps both means, both variances, simultaneous concentration and both margins; labels may be randomized and $A$ is integer-valued without an output bound.
--
--   Differences from the source:
--   - encoding: binary words and one-based coordinates → Fin-indexed bits, little-endian decoding, and block concatenation; reason: these are bijective encodings; invalid output codes remain failures
--   - encoding: independent samples from D → the product probability measure D^k; reason: integration and event measures give exactly the stated expectations and probabilities
--   - encoding: a uniform coordinate and samples outside that coordinate → normalized counting measure on Fin k times D^k, ignoring the selected sample; reason: the extra unused sample integrates out and changes no residual distribution
--   - generalization: the surrounding reconstruction application uses 0 < ε < 1 → any ε > 0 for which the stated success premise holds; reason: the premise forces ε ≤ 1 and the same projection argument includes perfect prediction ε = 1
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Lemma 6.3, printed p. 13 / PDF p. 16; §6.1 standing context printed p. 12 / PDF p. 15. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_Residuals
open MeasureTheory ProbabilityTheory

namespace IntegerSumAmplification.Main

theorem lemma_6_3 {n m k : ℕ} (hk : 0 < k) (D : Measure (LabeledInput n m))
    [IsProbabilityMeasure D] (A : (Fin k → Bits n) → ℤ) (ε : ℝ)
    (hε : 0 < ε)
    (hA : ε ≤ (productLaw D k).real {z | globalResidual A z = 0}) :
    (∫ z, bMinus D A z ∂D) = pMinus D A ∧
    (∫ z, bPlus D A z ∂D) = pPlus D A ∧
    variance (bMinus D A) D ≤ 1 / (4 * (k : ℝ)) ∧
    variance (bPlus D A) D ≤ 1 / (4 * (k : ℝ)) ∧
    1 - 8 / ((k : ℝ) * ε ^ 2) ≤ D.real {z |
      |bMinus D A z - pMinus D A| ≤ ε / 4 ∧
      |bPlus D A z - pPlus D A| ≤ ε / 4} ∧
    (∀ z, (|bMinus D A z - pMinus D A| ≤ ε / 4 ∧
      |bPlus D A z - pPlus D A| ≤ ε / 4) →
      bMinus D A z ≤ targetLevel D A - ε / 4 ∧
      targetLevel D A + ε / 4 ≤ bPlus D A z) := by sorry

end IntegerSumAmplification.Main
