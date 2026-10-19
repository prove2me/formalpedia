-- Prove2me | Theorems.Thm_OAI_Erdos3_twoBoxDifferenceDensity_mem_Icc_s2
-- name    : OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:47.922292+00:00
-- url     : https://prove2.me/theorems/c4a50a9f-d2eb-445d-a01f-9de0475b45f5
-- title:
--   The two-box difference density takes values between zero and the linear box density cap
-- statement:
--   All named objects below are defined by OpenAI. Let $\iota$ be a finite type, $\ell, r : \iota \to \mathbb{R}$ with $\ell_i > 0$ and $r_i > 0$ for all $i$, let $A, B$ be continuous linear automorphisms of $\mathbb{R}^\iota$, and let $x \in \mathbb{R}^\iota$. Write $W_\ell(u) = \prod_i \mathbf{1}[u_i \in (0, \ell_i]]/\ell_i$ for the uniform probability density on the box $\prod_i (0, \ell_i]$ (`boxProbabilityWindow ℓ 0`). Let `linearBoxDensity r B` be the function $y \mapsto |\det B^{-1}|\, W_r(B^{-1}y)$ (the density of the image under $B$ of the uniform distribution on $\prod_i (0, r_i]$), and let
--   $$\texttt{twoBoxDifferenceDensity}\ \ell\ r\ A\ B\ (x) = \int_{\mathbb{R}^\iota} W_\ell(u)\cdot \texttt{linearBoxDensity}\ r\ B\ (x + Au)\,du.$$
--   Then
--   $$0 \le \texttt{twoBoxDifferenceDensity}\ \ell\ r\ A\ B\ (x) \le \texttt{linearBoxDensityCap}\ r\ hr\ B = |\det B^{-1}|\prod_i \frac{1}{r_i}.$$
--
--   Lean: `OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc_s2`, which states OpenAI's `OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc` (in `lean/OAI/Combinatorics/Progressions/Geometry/TwoBoxSmoothingComplex.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B061` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/TwoBoxSmoothingComplex.lean (declaration OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B061

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem twoBoxDifferenceDensity_mem_Icc_s2 (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    twoBoxDifferenceDensity ℓ r A B x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap r hr B) := by
  sorry

end Erdos3

end

end OAI
end
