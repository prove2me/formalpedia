-- Prove2me | Theorems.Thm_LevelSetScores_lintegral_weightedMass
-- name    : LevelSetScores.lintegral_weightedMass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:29.396307+00:00
-- url     : https://prove2.me/theorems/b77c02c0-86ea-43f7-9123-43c79823dc13
-- title:
--   Proof of Theorem 2, p. 34: $\mathbb E_{P_Y}[\vartheta(\bullet,z)] = \Xi[Y](z)$ (Fubini step)
-- statement:
--   Throughout, $\mathbb R^d$ carries its Borel $\sigma$-algebra and Lebesgue measure. Let $h \ge 0$ be a measurable integrable function, $d\lambda(z) = h(z)\,dz$, let the kernel $w$ be an s-finite measure $\nu$ on $\mathbb R^d$, let $P$ be a measure on $\mathbb R^d$ (the law $P_Y$ of the observation $Y$), and let $\Xi$ be a measurable Lebesgue density of the convolution $P * \nu$ (the paper's $\Xi[Y] = f_Y * w$). For a Borel set $B$ and $y \in \mathbb R^d$ write $\mu_{y,w}(B) = \int \mathbb 1\{y+u \in B\}\, h(y+u)\, d\nu(u)$, i.e. $\int w(z-y)\mathbb 1\{z\in B\} h(z)\,dz$, and $S(B, y) = \alpha\lambda(B) - \mu_{y,w}(B)$ for the score (11).
--
--   Let $h$ be measurable (no sign or integrability condition is needed here). For every Borel set $B \subseteq \mathbb R^d$,
--   $$\int \mu_{y,w}(B)\, dP(y) = \int_B h(z)\,\Xi(z)\, dz \qquad\text{in } [0,\infty].$$
--
--   This is the integrated form of the paper's identity $\mathbb E_{P_Y}[w(z - \bullet)] = \Xi[Y](z)$: the expected kernel-weighted mass of $B$ is the $\lambda$-integral of the smoothed density over $B$. It turns every expected score into an integral over $\mathbb R^d$.
--
--   **Formalization Note** $h$ and $\Xi$ enter through `ENNReal.ofReal`, i.e. as $\max(h,0)$ and $\max(\Xi,0)$; the identity is between lower Lebesgue integrals.
--
--   Differences from the source:
--   - reading: f_Y ∗ w, the convolution of the generalized density f_Y (PDF, pmf or mixture) with w, used both as a local Borel measure (Assumption 1(a)) and as a function (Ξ[Y] := (f_Y ∗ w)(z), p. 33) → Ξ is any measurable Lebesgue density of the measure Measure.conv P ν (hypothesis hΞ); reason: for a function kernel w and every P this density is z ↦ ∫ w(z − s) dP_Y(s), the convolution of p. 6; null-set changes of Ξ change no expected score
--   - reading: the pointwise identity E_{P_Y}[ϑ(•,z)] = Ξ[Y](z) → its integral against 1_B(z) h(z) dz for every Borel B, in ℝ≥0∞; reason: for a measure kernel ϑ(y,z) = w(z − y) has no pointwise value; the pointwise identity is the hypothesis hΞ itself, and the proof uses it only in this integrated form (passing from ∆′′ to (19))
--   - generalization: w a nonnegative local Borel measure (Assumption 1(a)) → ν any s-finite measure on ℝᵈ; w(z − y) is integrated as ∫ φ(y + u) dν(u); reason: locally finite Borel measures on ℝᵈ are s-finite and nonnegative; a function kernel w ≥ 0 is volume.withDensity w and δ₀ is dirac 0, so the source's kernels are instances
--   - generalization: P_Y a probability measure in V^d; h ≥ 0 integrable → P any measure; h only measurable (entering as max(h, 0)); reason: the identity holds without these conditions; for a probability P and h ≥ 0 it is the source's
--   - generalization: ℝ^d (d ≥ 1 implicitly) → EuclideanSpace ℝ (Fin d) for every d : ℕ, including d = 0; reason: the d = 0 instance (a point) is extra and the statement specializes to the source for d ≥ 1
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, proof of Theorem 2 (ii), unnumbered, pp. 33–34 ('Notice that EPY[ϑ(•,z)] = Ξ[Y](z)', p. 34)

import Mathlib
import Definitions.Def_LevelSetScores_weightedMass

open MeasureTheory
open scoped ENNReal

namespace LevelSetScores

/-- **Fubini step: `E_{P_Y}[ϑ(•,z)] = Ξ[Y](z)` integrated over a set.**
Meng, Taylor, Ben Taieb, Li, *Scores for Multivariate Distributions and Level Sets*,
arXiv:2002.09578v6, proof of Theorem 2 (ii), unnumbered, pp. 33–34: "For notational
convenience, for any PX ∈ Vd we write ϑ(y,z) := w(z − y), and Ξ[Y](z) := (fY ∗ w)(z)."
(p. 33) and "Notice that EPY[ϑ(•,z)] = Ξ[Y](z), which implies that" (p. 34).

For every measurable `B`, the `P`-expectation of the weighted mass `µ_{y,w}(B)` is
`∫_B h(z) Ξ(z) dz`, where `Ξ` is a Lebesgue density of the convolution `P ∗ ν`.

**Formalization Note.** The kernel `w` is the s-finite measure `ν` and `f_Y ∗ w` is a Lebesgue
density `Ξ` of `Measure.conv P ν` (hypothesis `hΞ`); `P` may be any measure. The identity is in
`ℝ≥0∞`, so no integrability is needed; `h` and `Ξ` enter through `ENNReal.ofReal`. -/
theorem lintegral_weightedMass {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh_meas : Measurable h)
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [SFinite ν]
    {P : Measure (EuclideanSpace ℝ (Fin d))}
    {Ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hΞ_meas : Measurable Ξ)
    (hΞ : Measure.conv P ν = volume.withDensity (fun z => ENNReal.ofReal (Ξ z)))
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    ∫⁻ y, weightedMass h ν B y ∂P =
      ∫⁻ z in B, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z) := by sorry

end LevelSetScores
