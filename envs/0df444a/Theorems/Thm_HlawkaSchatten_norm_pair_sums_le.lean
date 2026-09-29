-- Prove2me | Theorems.Thm_HlawkaSchatten_norm_pair_sums_le
-- name    : HlawkaSchatten.norm_pair_sums_le
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:19:39.634793+00:00
-- url     : https://prove2.me/theorems/f221b0ac-4a07-4bc3-a378-dfed3ff1614b
-- title:
--   Hlawka's inequality for the norm of any real or complex inner-product space
-- statement:
--   Let $E$ be a vector space carrying an inner product over a scalar field $\mathbb{K}$ that is either the real numbers $\mathbb{R}$ or the complex numbers $\mathbb{C}$ (Mathlib's `RCLike` typeclass covers both cases at once), and let $\|\cdot\|$ denote the norm induced by that inner product. For any three vectors $x,y,z\in E$,
--
--   $$
--   \|x+y\| + \|x+z\| + \|y+z\| \;\le\; \|x\| + \|y\| + \|z\| + \|x+y+z\|.
--   $$
--
--   This is Hlawka's inequality in its classical form, valid in every real or complex inner-product space with no restriction on the dimension of $E$. A real-valued functional $N$ on a normed additive group is said to *have Hlawka constant* $C$ when $N(x)+N(y)+N(z)-N(x+y+z)\le C\big[(N(x)+N(y)-N(x+y))+(N(x)+N(z)-N(x+z))+(N(y)+N(z)-N(y+z))\big]$ for all $x,y,z$; rearranged, the inequality says exactly that an inner-product norm has Hlawka constant $1$. Other size functionals are compared against an inner-product norm after being mapped into an auxiliary inner-product space: whenever a (possibly nonlinear) map into such a space preserves the size of every individual vector, this inequality bounds the mapped triple deficit by the mapped pair-deficit sum, which is the last ordered-algebraic ingredient needed to transfer a Hlawka constant back to the original functional.
--
--   **Formalization Note** The theorem is stated once for a generic `RCLike` scalar field, so a single Lean proof covers both the real and the complex inner-product case.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HilbertHlawka.lean#L66-L91

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Hlawka's inequality in inner-product spaces

This proof uses the quadrilateral square identity. It avoids the Gaussian
integration route from the paper while proving the same Hilbert-space layer.
-/




variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

include 𝕜

theorem HlawkaSchatten.norm_pair_sums_le (x y z : E) :
    ‖x + y‖ + ‖x + z‖ + ‖y + z‖ ≤
      ‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖ := by sorry
