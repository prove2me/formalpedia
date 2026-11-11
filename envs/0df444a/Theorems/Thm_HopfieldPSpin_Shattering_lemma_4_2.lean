-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_2
-- name    : HopfieldPSpin.Shattering.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:26.885397+00:00
-- url     : https://prove2.me/theorems/83549804-bd25-47a2-8c8c-1700abe44c5f
-- title:
--   Lemma 4.2 — $\Lambda_p\to2\log2$
-- statement:
--   Let $I(t)=\log2-h(\frac{1-t}2)$ and $\Lambda_p=\inf_{0<t\le1}\frac{1+t^p}{t^p}I(t)$. Then
--   $$\lim_{p\to\infty}\Lambda_p=2\log2 .$$
--   $\Lambda_p$ is the second-moment threshold: $\beta^2<\Lambda_p$ is what the proof of Theorem 4.10 needs, and Lemma 4.2 makes it hold for every $\beta<\sqrt{2\log2}$ once $p$ is large.
--
--   Differences from the source:
--   - encoding: $\Lambda_p$ defined for $p>2$, limit over integers $p\to\infty$ → `lambdaP p` defined for every natural $p$ as a real infimum over the subtype $(0,1]$; `Tendsto … atTop`; reason: the limit only sees large $p$; the infimum is over a nonempty set of nonnegative values, so it is the true one
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 16 (PDF 18), Lemma 4.2, (4.4), (4.7)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Entropy

open Filter Topology

namespace HopfieldPSpin.Shattering

/-- Lemma 4.2 (p. 16): `Λ_p → 2 log 2` as `p → ∞`. -/
theorem lemma_4_2 : Tendsto (fun p : ℕ => lambdaP p) atTop (𝓝 (2 * Real.log 2)) := by sorry

end HopfieldPSpin.Shattering
