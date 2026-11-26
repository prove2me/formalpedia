-- Prove2me | Theorems.Thm_MathlibGap_absolutelyContinuous_pi
-- name    : MathlibGap.absolutelyContinuous_pi
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:53:52.610803+00:00
-- url     : https://prove2.me/theorems/3d8fb7df-4a8a-4955-b973-74f3dde8a4a7
-- title:
--   Absolute continuity passes to finite product measures
-- statement:
--   Let $\iota$ be a finite index set and, for each $i \in \iota$, let $\mu_i$ and $\nu_i$ be $\sigma$-finite measures on a measurable space $\alpha_i$. If $\mu_i \ll \nu_i$ for every $i$, then the product measures satisfy
--
--   $$
--   \bigotimes_{i \in \iota} \mu_i \ \ll\ \bigotimes_{i \in \iota} \nu_i .
--   $$
--
--   In words: a set that is null for the product of the $\nu_i$ is null for the product of the $\mu_i$. A typical use is showing that a lower-dimensional set has probability zero under a product of laws with densities, by comparing with the product of Lebesgue measures.
--
--   **Formalization Note** The products are `MeasureTheory.Measure.pi`. Mathlib at this revision has the two-factor version `MeasureTheory.Measure.AbsolutelyContinuous.prod` but no finite-product version; this theorem fills that gap. It lives in the neutral namespace `MathlibGap` so it cannot clash with a future Mathlib lemma.
-- source:
--   Standard measure theory, a consequence of the Radon-Nikodym theorem and the density of a product measure; see e.g. G. B. Folland, Real Analysis, 2nd ed., Section 2.5 (product measures) and Section 3.2 (Radon-Nikodym). Fills a gap in Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, which has only the binary case MeasureTheory.Measure.AbsolutelyContinuous.prod.

import Mathlib

open MeasureTheory

namespace MathlibGap

theorem absolutelyContinuous_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {μ ν : (i : ι) → Measure (α i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (h : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by sorry

end MathlibGap
