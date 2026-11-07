-- Prove2me | Theorems.Thm_MatrixSpencer_lemma_2_3
-- name    : MatrixSpencer.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:15.841208+00:00
-- url     : https://prove2.me/theorems/77d37e55-b02a-4943-a073-dd25328d0be3
-- title:
--   Lemma 2.3, p.7 — Hargé's convex comparison
-- statement:
--   Let $\gamma_n$ be the standard Gaussian measure on $\mathbb R^n$ and $U:\mathbb R^n\to(-\infty,+\infty]$ a proper, lower semicontinuous, even, convex function with $0<Z:=\int e^{-U}d\gamma_n<\infty$. Let $d\mu=Z^{-1}e^{-U}d\gamma_n$. Then every convex $\Phi:\mathbb R^n\to\mathbb R$ integrable under $\gamma_n$ is integrable under $\mu$ and
--
--   $$\mathbb E_\mu\Phi(g)\le\mathbb E_{\gamma_n}\Phi(g).$$
--
--   It says that an even log-concave tilt makes the Gaussian measure more concentrated in convex order, and it controls moments under the tilted measures of the proof.
--
--   **Formalization Note** $U$ is given by its domain $D$ and its finite values on $D$, through the published `GoldenRatioVI.IsProperConvexLsc`.
--
--   Differences from the source:
--   - encoding: U : ℝⁿ → (−∞, +∞] → the pair (D, U) with D = {U < +∞}, through the published GoldenRatioVI.IsProperConvexLsc; reason: the same objects; proper means D nonempty, and lower semicontinuity is that of the extended function
--   - encoding: 0 < Z < ∞ → 0 < ∫_D e^{−U} dγₙ; reason: a non-integrable Bochner integral is 0 in Lean, so this carries Z < ∞
--   - encoding: E_µΦ is implicitly well defined → integrability of Φe^{−U} on D is in the conclusion; reason: so no junk integral is read; it follows from the printed hypotheses, as e^{−U} is bounded
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.3, p.7 (PDF p.9), citing [Har04, Theorem 1.1]

import Mathlib
import Definitions.Def_MatrixSpencer_gam
import Definitions.Def_GoldenRatioVI_IsProperConvexLsc
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **Lemma 2.3 (Hargé's convex comparison).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.3, p.7 (PDF p.9), citing [Har04, Theorem 1.1]: "Let γₙ be standard Gaussian measure on ℝⁿ.
Let U : ℝⁿ → (−∞, +∞] be a proper, lower semicontinuous, even convex function. Assume that
0 < Z := ∫_{ℝⁿ} e^{−U(g)} dγₙ(g) < ∞, and define dµ = Z⁻¹e^{−U} dγₙ. Then, every convex function
Φ : ℝⁿ → ℝ that is integrable under γₙ satisfies E_µΦ(g) ≤ E_{γₙ}Φ(g)."

**Formalization Note.** `U` is given by the published `GoldenRatioVI.IsProperConvexLsc D U`: its domain
`D = {U < +∞}` and finite values on `D`. So `e^{−U} = 0` off `D`, and `Z = ∫_D e^{−U} dγₙ`. A Bochner
integral of a non-integrable function is `0`, so `0 < Z` carries `Z < ∞`. Evenness is that of the
extended function. `E_µΦ` is `(∫_D Φe^{−U} dγₙ)/Z`, and the conclusion also states that this integrand
is integrable, so no junk value is read. -/
theorem lemma_2_3 {n : ℕ} (D : Set (E n)) (U : E n → ℝ)
    (hU : GoldenRatioVI.IsProperConvexLsc D U)
    (hD : ∀ x, x ∈ D ↔ -x ∈ D) (hEven : ∀ x ∈ D, U (-x) = U x)
    (hZ : 0 < ∫ g in D, Real.exp (-U g) ∂(gam n))
    (Φ : E n → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) (hΦi : MeasureTheory.Integrable Φ (gam n)) :
    MeasureTheory.IntegrableOn (fun g => Φ g * Real.exp (-U g)) D (gam n) ∧
      (∫ g in D, Φ g * Real.exp (-U g) ∂(gam n)) / (∫ g in D, Real.exp (-U g) ∂(gam n)) ≤
        ∫ g, Φ g ∂(gam n) := by sorry

end MatrixSpencer
