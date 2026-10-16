-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_finite_residue_discrepancy
-- name    : OAI.ShortEgyptian.finite_residue_discrepancy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:33:18.762891+00:00
-- url     : https://prove2.me/theorems/7623d80d-0231-4564-99a6-26be8a196ff0
-- title:
--   Small low-frequency Fourier coefficients force mass at least $\delta/2$ on the window $[0,\delta q)$
-- statement:
--   Let $q\ge1$ be an integer. For $x\in\mathbb{Z}/q\mathbb{Z}$ write $\bar x\in\{0,\dots,q-1\}$ for its least nonnegative representative, $e_q(x)=\exp(2\pi i\,\bar x/q)$, and $\|k\|_q=\min(\bar k,\,q-\bar k)$. For $\mu:\mathbb{Z}/q\mathbb{Z}\to\mathbb{R}$ define the Fourier coefficients
--   $$\widehat\mu(k)=\sum_{x\in\mathbb{Z}/q\mathbb{Z}}\mu(x)\,e_q(-kx),\qquad k\in\mathbb{Z}/q\mathbb{Z}.$$
--   Let $R_q(\delta)=\{\,n\bmod q:\ n\in\mathbb{N},\ n<\lceil\delta q\rceil\,\}$ be the residue window of relative length $\delta$; for $0<\delta\le1$ it consists exactly of the residues $x$ with $\bar x<\delta q$.
--
--   Let $0<\delta\le 1/256$, and let $H\ge1$ be an integer with $2H\delta^4\ge1$. Let $\mu$ be a probability vector on $\mathbb{Z}/q\mathbb{Z}$, i.e. $\mu(x)\ge0$ for all $x$ and $\sum_x\mu(x)=1$, such that
--   $$|\widehat\mu(k)|\le\delta^3\qquad\text{for every }k\neq0\text{ with }\|k\|_q\le H .$$
--   Then
--
--   $$
--   \sum_{x\in R_q(\delta)}\mu(x)\;\ge\;\frac{\delta}{2}.
--   $$
--
--   This is a one-sided discrepancy estimate: a distribution on $\mathbb{Z}/q\mathbb{Z}$ whose nonzero Fourier coefficients up to frequency $H\approx\delta^{-4}$ are all at most $\delta^3$ gives the initial window of relative length $\delta$ at least half of the mass $\delta$ that the uniform distribution would give it. No size condition on $q$ is needed. The estimate is applied to empirical distributions of finite families of residues.
--
--   **Formalization Note** The Fourier coefficient is `probabilityFourier μ k`, the sum of `μ x * ZMod.stdAddChar (-(k * x))`; the window is `residueWindow q δ = natWindow q ⌈δ * q⌉₊` (`Nat.ceil`); the distance is `frequencyDistance k = min k.val (q - k.val)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/WindowDiscrepancy.lean#L133-L209

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.finite_residue_discrepancy {q : ℕ} [NeZero q] (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256) (H : ℕ) (hH : 1 ≤ H)
    (hHδ : 1 ≤ 2 * (H : ℝ) * δ ^ 4)
    (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (hFourier : ∀ k : ZMod q, k ≠ 0 → frequencyDistance k ≤ H →
      ‖probabilityFourier μ k‖ ≤ δ ^ 3) :
    δ / 2 ≤ ∑ x ∈ residueWindow q δ, μ x := by sorry
