-- Prove2me | Theorems.Thm_LinfContractionFP_lemma_1
-- name    : LinfContractionFP.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:01.021804+00:00
-- url     : https://prove2.me/theorems/5cf5591c-ef6c-4faf-bd8d-962653a7cf64
-- title:
--   Lemma 1 — $\gamma\|x-x^*\|\le\|x-f(x)\|\le(2-\gamma)\|x-x^*\|$
-- statement:
--   Let $0<\gamma\le1$, let $f$ be a $(1-\gamma)$-contraction of $[0,1]^d$, extended to $\mathbb R^d$ by clipping, and let $x^*$ be its fixed point. For every $x\in\mathbb R^d$,
--   $$\gamma\,\|x-x^*\|_\infty\ \le\ \|x-f(x)\|_\infty\ \le\ (2-\gamma)\,\|x-x^*\|_\infty .$$
--   The lemma converts approximate fixed points into near ones and back; with $\eta=\gamma\varepsilon$ it turns ThinLabel's $\eta$-approximate fixed points into $\varepsilon$-near ones.
--
--   Differences from the source:
--   - encoding: f (the clipped extension, Section 3) → clipExt f, with x* given as a point of the cube fixed by f; reason: the paper's standing convention made explicit
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Lemma 1, p.5

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_clipExt

namespace LinfContractionFP

/-- Lemma 1: for every `x ∈ ℝ^d`, `γ ‖x − x*‖∞ ≤ ‖x − f(x)‖∞ ≤ (2 − γ) ‖x − x*‖∞`, with `f` the
clipped extension and `x*` the fixed point.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Lemma 1, p.5: "Lemma 1. For every x ∈ R^d, γ ‖x − x*‖∞ ≤ ‖x − f(x)‖∞ ≤ (2 − γ) ‖x − x*‖∞."

**Formalization Note.** `f` is replaced by `clipExt f`, the paper's standing extension
(Section 3), because `x` ranges over all of `ℝ^d`. `xs` is the fixed point (in the cube). -/
theorem lemma_1 {ι : Type} [Fintype ι] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : IsContraction γ f) (xs : ι → ℝ) (hxs : xs ∈ unitCube ι)
    (hfix : f xs = xs) (x : ι → ℝ) :
    γ * ‖x - xs‖ ≤ ‖x - clipExt f x‖ ∧ ‖x - clipExt f x‖ ≤ (2 - γ) * ‖x - xs‖ := by sorry

end LinfContractionFP
