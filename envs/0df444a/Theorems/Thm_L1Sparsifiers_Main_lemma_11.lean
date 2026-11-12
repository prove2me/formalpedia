-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_lemma_11
-- name    : L1Sparsifiers.Main.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:35.92492+00:00
-- url     : https://prove2.me/theorems/2edaed91-7882-4223-b37c-44ca47d17996
-- title:
--   Lemma 11 — support density bounds $\|f\|_p$ by $\|f\|_2$
-- statement:
--   Let $f:\{-1,1\}^m\to\mathbb R$ and $1\le p<2$. Write $\|g\|_q=\big(\mathbb E_{x\sim\{-1,1\}^m}|g(x)|^q\big)^{1/q}$ for the uniform distribution on the vertices, and let
--   $$\alpha=\mathbb P_{x\sim\{-1,1\}^m}[f(x)\ne0]$$
--   be the density of the support of $f$. Then
--   $$\|f\|_p\le\alpha^{1/p-1/2}\,\|f\|_2 .$$
--   The case $\alpha=0$ ($f\equiv0$) is included.
--
--   Combined with hypercontractivity, this converts a lower bound on a noisy $\ell_2$ norm into a lower bound on the support density, as in Lemma 18.
--
--   **Formalization Note** The norm is the published `PSDPolyApprox.lpNorm`, and $\alpha$ is the published `PSDPolyApprox.expect` of the indicator of $f\ne0$. Powers are real powers.
--
--   Differences from the source:
--   - encoding: {−1,1}^m and P_{x∼{−1,1}^m} → PSDPolyApprox.Cube m = Fin m → ℤˣ; α = 2^{−m} Σ_x 1[f(x) ≠ 0]; reason: ℤˣ = {±1}; same instances
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §2, Lemma 11, p.6

import Mathlib
import Definitions.Def_PSDPolyApprox_lpNorm

namespace L1Sparsifiers.Main

open PSDPolyApprox

/-- **Lemma 11** (p.6). "Let f : {−1,1}^m → ℝ and 1 ≤ p < 2. Then ‖f‖_p ≤ α^{1/p−1/2} ‖f‖₂ where
α := P_{x∼{−1,1}^m}[f(x) ≠ 0] is the density of the support."

`‖f‖_p = (E|f|^p)^{1/p}` under the uniform measure on the vertices (published `lpNorm`), and
`α = E[𝟙_{f ≠ 0}]` (published `expect`). Real powers; `α = 0` is included. -/
theorem lemma_11 {m : ℕ} (f : Cube m → ℝ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2) :
    lpNorm p f ≤
      (expect (fun x => if f x ≠ 0 then (1 : ℝ) else 0)) ^ (1 / p - 1 / 2) * lpNorm 2 f := by sorry

end L1Sparsifiers.Main
