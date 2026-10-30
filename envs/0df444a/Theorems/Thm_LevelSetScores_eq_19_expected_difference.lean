-- Prove2me | Theorems.Thm_LevelSetScores_eq_19_expected_difference
-- name    : LevelSetScores.eq_19_expected_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:00.507079+00:00
-- url     : https://prove2.me/theorems/c55fd156-791a-4dad-9620-a79af04f7090
-- title:
--   Eq. (19): the expected score difference $\Delta'$ as an integral over $\mathbb R^d$
-- statement:
--   Throughout, $\mathbb R^d$ carries its Borel $\sigma$-algebra and Lebesgue measure. Let $h \ge 0$ be a measurable integrable function, $d\lambda(z) = h(z)\,dz$, let the kernel $w$ be an s-finite measure $\nu$ on $\mathbb R^d$, let $P$ be a probability measure on $\mathbb R^d$ (the law $P_Y$ of the observation $Y$), and let $\Xi$ be a measurable Lebesgue density of the convolution $P * \nu$ (the paper's $\Xi[Y] = f_Y * w$). For a Borel set $B$ and $y \in \mathbb R^d$ write $\mu_{y,w}(B) = \int \mathbb 1\{y+u \in B\}\, h(y+u)\, d\nu(u)$, i.e. $\int w(z-y)\mathbb 1\{z\in B\} h(z)\,dz$, and $S(B, y) = \alpha\lambda(B) - \mu_{y,w}(B)$ for the score (11).
--
--   Assume in addition that $\Xi \ge 0$ everywhere. Let $\alpha > 0$, $U = \{\Xi > \alpha\}$, and let $A$ be a Borel set. Suppose that $\mu_{y,w}(A) < \infty$ and $\mu_{y,w}(U) < \infty$ for $P$-a.e. $y$, and that $y \mapsto S(A,y)$ and $y \mapsto S(U,y)$ are $P$-integrable. With $\Sigma_{+-} = A \cap \{\Xi \le \alpha\}$ and $\Sigma_{-+} = A^c \cap \{\Xi > \alpha\}$,
--   $$\mathbb E_P[S(A,Y)] - \mathbb E_P[S(U,Y)] = \int_{\mathbb R^d} \big(\alpha - \Xi(z)\big)\big[\mathbb 1_{\Sigma_{+-}}(z) - \mathbb 1_{\Sigma_{-+}}(z)\big]\, h(z)\, dz.$$
--
--   This is the identity $\Delta' = \mathbb E_{P_Y}[\Delta''] = \int \{(\alpha - \Xi[Y])[\mathbb 1_{\Sigma_{+-}} - \mathbb 1_{\Sigma_{-+}}]\} h\, dz$ of the paper; the sign of the integrand then gives consistency.
--
--   Differences from the source:
--   - reading: f_Y ∗ w, the convolution of the generalized density f_Y (PDF, pmf or mixture) with w, used both as a local Borel measure (Assumption 1(a)) and as a function (Ξ[Y] := (f_Y ∗ w)(z), p. 33) → Ξ is any measurable Lebesgue density of the measure Measure.conv P ν (hypothesis hΞ); reason: for a function kernel w and every P this density is z ↦ ∫ w(z − s) dP_Y(s), the convolution of p. 6; null-set changes of Ξ change no expected score
--   - encoding: f_Y ∗ w is nonnegative for nonnegative w (p. 33) → hypothesis hΞ_nonneg : ∀ z, 0 ≤ Ξ z (a nonnegative version of the density); reason: hΞ fixes Ξ only through max(Ξ, 0); the paper's Ξ[Y] is nonnegative, and choosing a nonnegative version changes no instance
--   - reading: ∆′ = E_{P_Y}[∆′′] for an arbitrary Borel A, hypotheses stated for A only → finiteness and integrability hypotheses for A and for U = {Ξ > α}; reason: the step compares two expected scores as real numbers, which needs both finite; the preceding milestone supplies them for U from the hypotheses on L(f_Y ∗ w; α)
--   - generalization: w a nonnegative local Borel measure (Assumption 1(a)) → ν any s-finite measure on ℝᵈ; w(z − y) is integrated as ∫ φ(y + u) dν(u); reason: locally finite Borel measures on ℝᵈ are s-finite and nonnegative; a function kernel w ≥ 0 is volume.withDensity w and δ₀ is dirac 0, so the source's kernels are instances
--   - generalization: P_Y in a convex class V^d of probability measures satisfying Assumption 1 → P any Borel probability measure on ℝᵈ (subject to hΞ); reason: the claim is about each P_Y separately; the class V^d plays no role in it
--   - generalization: (S′)Γ(A,•;w,h,α) finite L^d-a.e. and (S′)Γ(A,•;w,h,α) f_Y(•) integrable → µ_{y,w}(A) < ∞ for P-a.e. y, and y ↦ (S′)Γ(A,y;w,h,α) is P-integrable; reason: for P_Y with a Lebesgue density L^d-a.e. finiteness implies P-a.e. finiteness and 'S f_Y integrable' is P-integrability; for laws with atoms only the P-a.e. version gives the expectation a meaning
--   - generalization: ℝ^d (d ≥ 1 implicitly) → EuclideanSpace ℝ (Fin d) for every d : ℕ, including d = 0; reason: the d = 0 instance (a point) is extra and the statement specializes to the source for d ≥ 1
--   - encoding: h a nonnegative integrable Radon–Nikodym derivative of λ (Assumption 1(a)) → h measurable, h z ≥ 0 for every z, Integrable h; reason: a Radon–Nikodym derivative is Borel measurable and can be chosen pointwise nonnegative; the pointwise version matters for w = δ₀, where the score evaluates h(y) ((12), p. 15)
--   - encoding: (S′)Γ(A,y;w,h,α) = ∫ (α − w(z − y)) 1{z ∈ A} h(z) dz (11) → α ∫_A h − (µ_{y,w}(A)).toReal (levelSetScore), the split used by the paper in ∆′′ (p. 33); reason: the two agree whenever µ_{y,w}(A) < ∞; toReal returns 0 at ∞, and every theorem assumes the mass finite P-a.e.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, proof of Theorem 2 (ii), display (19), p. 34 (Σ+−, Σ−+ defined on p. 33)

import Mathlib
import Definitions.Def_LevelSetScores_weightedMass
import Definitions.Def_LevelSetScores_levelSetScore

open MeasureTheory
open scoped ENNReal

namespace LevelSetScores

/-- **The expected score difference (19).**
Meng, Taylor, Ben Taieb, Li, *Scores for Multivariate Distributions and Level Sets*,
arXiv:2002.09578v6, proof of Theorem 2 (ii), display (19), p. 34:
"∆′ = EPY[∆′′] = ∫Rd {(α − Ξ[Y](z))[1Σ+−(z) − 1Σ−+(z)]} h(z) dz.", with (p. 33)
"Σ+− := A ∩ {Ξ[Y] ≤ α}" and "Σ−+ := Ac ∩ {Ξ[Y] > α}".

If `A` and `U = {Ξ > α}` are measurable with `P`-a.e. finite weighted mass and `P`-integrable
scores, then `E_P[S(A, ·)] − E_P[S(U, ·)]` equals
`∫ (α − Ξ(z)) (1_{A ∩ {Ξ ≤ α}}(z) − 1_{Aᶜ ∩ {Ξ > α}}(z)) h(z) dz`.

**Formalization Note.** The kernel `w` is the s-finite measure `ν`, `f_Y ∗ w` is a Lebesgue
density `Ξ` of `Measure.conv P ν`, and the score is `levelSetScore` (display (11)). The paper
notes that `f_Y ∗ w` is nonnegative for nonnegative `w` (p. 33); the hypothesis `hΞ_nonneg`
selects a nonnegative version of the density, which is needed because the density enters
`Measure.conv P ν` only through `ENNReal.ofReal Ξ`. -/
theorem eq_19_expected_difference {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [SFinite ν]
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]
    {Ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hΞ_meas : Measurable Ξ)
    (hΞ : Measure.conv P ν = volume.withDensity (fun z => ENNReal.ofReal (Ξ z)))
    (hΞ_nonneg : ∀ z, 0 ≤ Ξ z)
    {α : ℝ} (hα : 0 < α)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    (hA_fin : ∀ᵐ y ∂P, weightedMass h ν A y ≠ ∞)
    (hA_int : Integrable (levelSetScore h ν α A) P)
    (hU_fin : ∀ᵐ y ∂P, weightedMass h ν {z | α < Ξ z} y ≠ ∞)
    (hU_int : Integrable (levelSetScore h ν α {z | α < Ξ z}) P) :
    ∫ y, levelSetScore h ν α A y ∂P - ∫ y, levelSetScore h ν α {z | α < Ξ z} y ∂P =
      ∫ z, (α - Ξ z) * ((A ∩ {z | Ξ z ≤ α}).indicator 1 z -
        (Aᶜ ∩ {z | α < Ξ z}).indicator 1 z) * h z := by sorry

end LevelSetScores
