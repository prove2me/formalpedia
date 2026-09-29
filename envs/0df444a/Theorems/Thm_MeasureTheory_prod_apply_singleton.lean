-- Prove2me | Theorems.Thm_MeasureTheory_prod_apply_singleton
-- name    : MeasureTheory.prod_apply_singleton
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:26:05.603344+00:00
-- url     : https://prove2.me/theorems/17dd4c29-4fc6-43bc-9b63-384ef2500691
-- title:
--   The product measure of a singleton factors
-- statement:
--   **A product measure evaluated at a point is the product of the point masses.**
--
--   For $\sigma$-finite $\nu$ and any point $x = (x_1, x_2) \in \alpha \times \beta$,
--
--   $$(\mu \otimes \nu)\bigl(\{x\}\bigr) \;=\; \mu\bigl(\{x_1\}\bigr)\,\nu\bigl(\{x_2\}\bigr).$$
--
--   The singleton $\{(x_1,x_2)\}$ is the measurable rectangle $\{x_1\} \times \{x_2\}$, so this is
--   the defining property of the product measure specialised to a rectangle whose sides are
--   singletons. Note that no measurability or atomicity hypothesis on the singletons is needed —
--   the identity holds in general, both sides being $0$ when either factor is non-atomic at its
--   coordinate.
--
--   The statement matters for **discrete** or atomic components of a measure: it is what lets one
--   compute the mass a product measure assigns to individual points, which is the starting point
--   for treating a joint distribution of two random variables as a product when they are
--   independent, and for entropy computations where $\mathbb{P}(X = x_1, Y = x_2)$ must be split.
--
--   **Formalization note.** Values are in $[0,\infty]$ (`ENNReal`), so the product on the right is
--   the extended-real product; `SigmaFinite ν` is Mathlib's standing hypothesis for `Measure.prod`
--   to be well behaved.
-- source:
--   Adapted from the Polynomial Freiman–Ruzsa (PFR) project, upstream file `PFR/Mathlib/MeasureTheory/Measure/Prod.lean` (original authors Terence Tao and the PFR project contributors, Apache-2.0), as vendored in `Salt/Entropy/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MeasureTheory

open MeasureTheory Measure in
theorem prod_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by sorry

end MeasureTheory
