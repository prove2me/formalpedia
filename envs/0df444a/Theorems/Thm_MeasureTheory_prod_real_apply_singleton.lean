-- Prove2me | Theorems.Thm_MeasureTheory_prod_real_apply_singleton
-- name    : MeasureTheory.prod_real_apply_singleton
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:26:04.275403+00:00
-- url     : https://prove2.me/theorems/b072cd0c-e3db-42d8-b998-a685489ffc14
-- title:
--   The real-valued product measure of a singleton factors
-- statement:
--   **The real-valued version of the product-measure singleton identity.**
--
--   For $\sigma$-finite $\nu$ and $x = (x_1,x_2)$,
--
--   $$(\mu \otimes \nu)_{\mathbb{R}}\bigl(\{x\}\bigr)
--   \;=\; \mu_{\mathbb{R}}\bigl(\{x_1\}\bigr)\,\nu_{\mathbb{R}}\bigl(\{x_2\}\bigr),$$
--
--   where $\rho_{\mathbb{R}}(S) = (\rho(S)).\mathrm{toReal}$ is the real-valued measure.
--
--   This is the $\mathbb{R}$-valued companion of the `ENNReal` statement. The two are not
--   interchangeable in practice: probability and information-theoretic arguments are carried out in
--   $\mathbb{R}$, where subtraction and logarithms are available, and passing from `ENNReal` to
--   `ℝ` requires knowing the values are finite. Having the identity directly in real form avoids
--   that bookkeeping at every use.
--
--   It is the identity behind the factorisation
--   $\mathbb{P}(X = x_1, Y = x_2) = \mathbb{P}(X = x_1)\mathbb{P}(Y = x_2)$ for independent discrete
--   random variables, and hence behind the additivity of Shannon entropy over independent pairs.
--
--   **Formalization note.** `Measure.real` is Mathlib's real-valued measure; since
--   `ENNReal.toReal` is multiplicative on finite values and sends $\infty$ to $0$, the identity
--   requires a small case analysis rather than being a direct consequence of the `ENNReal` version.
-- source:
--   Adapted from the Polynomial Freiman–Ruzsa (PFR) project, upstream file `PFR/Mathlib/MeasureTheory/Measure/Prod.lean` (original authors Terence Tao and the PFR project contributors, Apache-2.0), as vendored in `Salt/Entropy/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MeasureTheory

open MeasureTheory Measure in
theorem prod_real_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by sorry

end MeasureTheory
