-- Prove2me | Theorems.Thm_MastSail_Monotone_lemma_1
-- name    : MastSail.Monotone.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:21.598512+00:00
-- url     : https://prove2.me/theorems/efcc49d4-7096-4eaf-83e1-6b49c6404976
-- title:
--   Lemma 1, p. 12 — the joint distribution function of inventory I and censored sales S = min{I, Q}
-- statement:
--   Let $0<\bar I\le\bar Q$, let $f$ be a probability density on $[0,\bar I]$ (the inventory density $f(\cdot\mid e_o)$) and $g$ a probability density on $[0,\bar Q]$ (the demand density $g(\cdot\mid e_m)$), with distribution functions $F(x)=\int_0^x f$ and $G(x)=\int_0^x g$. Let inventory $I$ and demand $Q$ be independent with these densities, and let $S=\min\{I,Q\}$ be the observed sales. Then for every $0\le s\le i\le\bar I$,
--   $$\Pr(I\le i,\ S\le s)=\begin{cases}F(s)+G(s)\,[F(i)-F(s)] & \text{if } s<i,\\ F(i) & \text{if } s=i.\end{cases}$$
--
--   The lemma is the reason the joint law of $(I,S)$ has a density $f(i)g(s)$ below the diagonal and a point mass $f(i)(1-G(i))$ on it, which is where the two ratio functions (9) and (10) come from.
--
--   **Formalization Note** The probability is computed under the product of the law with density $f$ on $[0,\bar I]$ and the law with density $g$ on $[0,\bar Q]$, with the event $\{I\le i,\ \min(Q,I)\le s\}$. The densities are assumed continuous and positive on their closed supports (the mission's standing convention); the lemma is stated for an arbitrary pair of densities, since it holds for every effort pair.
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, p. 12, Lemma 1 (proof pp. oa3–oa4)

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone
theorem lemma_1 (Ibar Qbar : ℝ) (f g : ℝ → ℝ) (hIbar : 0 < Ibar) (hIQ : Ibar ≤ Qbar)
    (hf : IsDensityOn 0 Ibar f) (hg : IsDensityOn 0 Qbar g)
    (i s : ℝ) (hs : 0 ≤ s) (hsi : s ≤ i) (hi : i ≤ Ibar) :
    (jointLaw Ibar Qbar f g {p : ℝ × ℝ | p.1 ≤ i ∧ min p.2 p.1 ≤ s}).toReal =
      if s < i then cdf f s + cdf g s * (cdf f i - cdf f s) else cdf f i := by sorry
end MastSail.Monotone
