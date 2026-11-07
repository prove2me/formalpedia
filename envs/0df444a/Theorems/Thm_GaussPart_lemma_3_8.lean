-- Prove2me | Theorems.Thm_GaussPart_lemma_3_8
-- name    : GaussPart.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:25.246985+00:00
-- url     : https://prove2.me/theorems/a99e7859-3674-4287-b79b-b1bd9fda22a9
-- title:
--   Lemma 3.8 — approximately bounded density ratio
-- statement:
--   Let $P,Q$ be probability distributions on a measurable space, with $Q$ $(q,\sigma)$-smooth with respect to $P$ ($q\ge1$, $\sigma\in(0,1]$), and let $f=dQ/dP$. For every $\varepsilon\in(0,1)$ the set
--   $$G=\Big\{x: f(x)\le\frac{1}{\sigma^q\varepsilon^{q-1}}\Big\}$$
--   satisfies $Q(G)\ge1-\varepsilon$, and $Q\mid G$ is $\big(1,(1-\varepsilon)\sigma^q\varepsilon^{q-1}\big)$-smooth with respect to $P$.
--
--   The lemma supplies the density-ratio hypothesis of Lemma 3.7 with $M=1/(\sigma^q\tau_0^{q-1})$.
--
--   **Formalization Note** $f$ is Mathlib's Radon–Nikodym derivative `Q.rnDeriv P` (with values in $[0,\infty]$); absolute continuity is not assumed, it follows from smoothness. Powers with real exponents are real powers.
--
--   Differences from the source:
--   - encoding: f = dQ/dP → Q.rnDeriv P; reason: a version of the density; another version changes G by a P-null, hence Q-null, set
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.8, p.22 (PDF p.24); proof Appendix C, p.73 (PDF p.75)

import Mathlib
import Definitions.Def_GaussPart_IsSmooth

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.8** (Approximately Bounded Density Ratio).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.8, p.22 (PDF p.24); proof in Appendix C,
p.73 (PDF p.75).

"Let P, Q be distributions on the same measurable space, with Q (q, σ)-smooth with respect to P,
where q ≥ 1 and σ ∈ (0, 1]. Write f = dQ/dP. For every ε ∈ (0, 1), the set
G = {x : f(x) ≤ 1/(σ^q ε^{q−1})} satisfies Q(G) ≥ 1 − ε. Moreover, Q | G is
(1, (1 − ε)σ^q ε^{q−1})-smooth with respect to P."

**Formalization Note.** `f` is Mathlib's `Q.rnDeriv P` (values in `ℝ≥0∞`); absolute continuity
`Q ≪ P` is not assumed, it follows from smoothness. Powers with the real exponents `q`, `q − 1` are
`Real.rpow` (at `q = 1`, `ε^0 = 1`). `Q | G` is `ProbabilityTheory.cond Q G`. -/
theorem lemma_3_8 {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (q σ : ℝ) (hq : 1 ≤ q) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hs : IsSmooth P Q q σ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ENNReal.ofReal (1 - ε) ≤
        Q {x | Q.rnDeriv P x ≤ ENNReal.ofReal (1 / (σ ^ q * ε ^ (q - 1)))} ∧
      IsSmooth P (ProbabilityTheory.cond Q
          {x | Q.rnDeriv P x ≤ ENNReal.ofReal (1 / (σ ^ q * ε ^ (q - 1)))})
        1 ((1 - ε) * σ ^ q * ε ^ (q - 1)) := by sorry

end GaussPart
