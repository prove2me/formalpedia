-- Prove2me | Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_1_5
-- name    : IsRandomnessNecessaryADA.Plain.lemma_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:16.089563+00:00
-- url     : https://prove2.me/theorems/3c72864e-4dc5-4907-950e-93f40c13e38e
-- title:
--   Lemma 1.5 — average conditional variation on the cube
-- statement:
--   Let $M\ge1$ and $d\ge0$ be integers. Let $X$ be uniform on the full sign cube $\{-1,+1\}^M$, let $f:\{-1,+1\}^M\to\{-1,+1\}^d$ be any function, and put $Y=f(X)$. Then
--   $$\frac1M\sum_{u=1}^M\operatorname{TV}\bigl(\mathcal L(Y\mid X_u=-1),\mathcal L(Y\mid X_u=+1)\bigr)\le\sqrt{\frac{2d}{M}}.$$
--   No linearity, balance, monotonicity or injectivity is required of $f$. In particular $d=0$ is allowed. The coordinate events have probability $1/2$. This controls the average dependence of an entire output vector on an individual input sign and supplies the response-profile bound.
--
--   Differences from the source:
--   - encoding: sign cubes indexed from 1, with M coordinates in the average → Bool function cubes on Fin M and Fin d, and explicit M>0; reason: false and true correspond bijectively to −1 and +1; positive M is the domain of the displayed coordinate average
--   - encoding: conditional law given a fair coordinate value → pushforward of the uniform cube by overwriting that coordinate; reason: this gives exactly the same positive-probability conditional distribution
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Lemma 1.5, p.5; proof §4.1, pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_ConditionalCube

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

/-- Lemma 1.5, p.5: the stated sqrt(2d/M), not a worse constant. -/
theorem lemma_1_5 (M d : ℕ) (hM : 0 < M)
    (f : (Fin M → Bool) → (Fin d → Bool)) :
    (∑ u : Fin M, pmfTV ((coordinateLaw u false).map f)
      ((coordinateLaw u true).map f)) / (M : ℝ) ≤ Real.sqrt (2 * (d : ℝ) / M) := by sorry

end IsRandomnessNecessaryADA.Plain
