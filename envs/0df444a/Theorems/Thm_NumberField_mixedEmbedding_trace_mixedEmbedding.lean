-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
-- name    : NumberField.mixedEmbedding.trace_mixedEmbedding
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4b4c8cc3-6d5b-58ba-8063-37253881613b
-- title:
--   Trace on the mixed space extends the field trace
-- statement:
--   Let $K$ be a number field and $x \in K$. Write $\mathrm{mixedSpace}\,K$ for the mixed (Minkowski) space of $K$, i.e. the product of a copy of $\mathbb{R}$ for each real infinite place and a copy of $\mathbb{C}$ for each complex infinite place, with its componentwise $\mathbb{R}$-algebra structure, and let $\mathrm{mixedEmbedding}\,K \colon K \to \mathrm{mixedSpace}\,K$ be the canonical algebra map sending $x$ to the family of its images under the infinite places. The assertion is the equality of real numbers
--   $$\operatorname{Tr}_{\mathrm{mixedSpace}\,K/\mathbb{R}}\bigl(\mathrm{mixedEmbedding}\,K\,(x)\bigr) = \operatorname{Tr}_{K/\mathbb{Q}}(x),$$
--   where the left-hand side is the trace of the $\mathbb{R}$-linear endomorphism of $\mathrm{mixedSpace}\,K$ given by multiplication by $\mathrm{mixedEmbedding}\,K\,(x)$, and the right-hand side is the trace of multiplication by $x$ on $K$ as a $\mathbb{Q}$-vector space, a rational number, viewed in $\mathbb{R}$ along the coercion $\mathbb{Q} \to \mathbb{R}$. Concretely this says $\sum_{w \text{ real}} w(x) + \sum_{w \text{ complex}} 2\operatorname{Re} w(x) = \operatorname{Tr}_{K/\mathbb{Q}}(x)$.
--
--   This is the trace compatibility underlying Minkowski theory: under the identification of $\mathrm{mixedSpace}\,K$ with $K \otimes_{\mathbb{Q}} \mathbb{R}$, the real trace form restricts on the image of $K$ to the trace form $(a,b) \mapsto \operatorname{Tr}_{K/\mathbb{Q}}(ab)$. It is used in the adelic Fourier analysis over a number field, where additive characters are built from the trace, and in the computation of determinants of trace forms in terms of the discriminant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_trace_mixedEmbedding.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.mixedEmbedding
open scoped Classical

theorem NumberField.mixedEmbedding.trace_mixedEmbedding
    (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by sorry
