-- Prove2me | Theorems.Thm_LevelSetScores_delta_prime_nonneg
-- name    : LevelSetScores.delta_prime_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:37.072322+00:00
-- url     : https://prove2.me/theorems/7864b3c6-13d7-4e03-ab84-144da2eae18e
-- title:
--   Proof of Theorem 2, p. 34: $\Delta' \ge 0$
-- statement:
--   Throughout, $\mathbb R^d$ carries its Borel $\sigma$-algebra and Lebesgue measure. Let $h \ge 0$ be a measurable integrable function, $d\lambda(z) = h(z)\,dz$, let the kernel $w$ be an s-finite measure $\nu$ on $\mathbb R^d$, let $P$ be a probability measure on $\mathbb R^d$ (the law $P_Y$ of the observation $Y$), and let $\Xi$ be a measurable Lebesgue density of the convolution $P * \nu$ (the paper's $\Xi[Y] = f_Y * w$). For a Borel set $B$ and $y \in \mathbb R^d$ write $\mu_{y,w}(B) = \int \mathbb 1\{y+u \in B\}\, h(y+u)\, d\nu(u)$, i.e. $\int w(z-y)\mathbb 1\{z\in B\} h(z)\,dz$, and $S(B, y) = \alpha\lambda(B) - \mu_{y,w}(B)$ for the score (11).
--
--   Let $\alpha > 0$, $U = \{\Xi > \alpha\}$, and let $A$ be a Borel set. Suppose that $\mu_{y,w}(A) < \infty$ and $\mu_{y,w}(U) < \infty$ for $P$-a.e. $y$, and that $y \mapsto S(A,y)$ and $y \mapsto S(U,y)$ are $P$-integrable. Then
--   $$\Delta' = \mathbb E_P[S(A,Y)] - \mathbb E_P[S(U,Y)] \ge 0, \quad\text{i.e.}\quad \mathbb E_P[S(U,Y)] \le \mathbb E_P[S(A,Y)].$$
--
--   This is the last step of the proof of consistency: the integrand of (19) is nonnegative, since $\alpha - \Xi \ge 0$ on $A \cap \{\Xi \le \alpha\}$ and $\alpha - \Xi < 0$ on $A^c \cap \{\Xi > \alpha\}$. No sign condition on $\Xi$ is needed.
--
--   Differences from the source:
--   - reading: f_Y ∗ w, the convolution of the generalized density f_Y (PDF, pmf or mixture) with w, used both as a local Borel measure (Assumption 1(a)) and as a function (Ξ[Y] := (f_Y ∗ w)(z), p. 33) → Ξ is any measurable Lebesgue density of the measure Measure.conv P ν (hypothesis hΞ); reason: for a function kernel w and every P this density is z ↦ ∫ w(z − s) dP_Y(s), the convolution of p. 6; null-set changes of Ξ change no expected score
--   - reading: ∆′ = E_{P_Y}[∆′′] for an arbitrary Borel A, hypotheses stated for A only → finiteness and integrability hypotheses for A and for U = {Ξ > α}; reason: the step compares two expected scores as real numbers, which needs both finite; the preceding milestone supplies them for U from the hypotheses on L(f_Y ∗ w; α)
--   - generalization: w a nonnegative local Borel measure (Assumption 1(a)) → ν any s-finite measure on ℝᵈ; w(z − y) is integrated as ∫ φ(y + u) dν(u); reason: locally finite Borel measures on ℝᵈ are s-finite and nonnegative; a function kernel w ≥ 0 is volume.withDensity w and δ₀ is dirac 0, so the source's kernels are instances
--   - generalization: P_Y in a convex class V^d of probability measures satisfying Assumption 1 → P any Borel probability measure on ℝᵈ (subject to hΞ); reason: the claim is about each P_Y separately; the class V^d plays no role in it
--   - generalization: (S′)Γ(A,•;w,h,α) finite L^d-a.e. and (S′)Γ(A,•;w,h,α) f_Y(•) integrable → µ_{y,w}(A) < ∞ for P-a.e. y, and y ↦ (S′)Γ(A,y;w,h,α) is P-integrable; reason: for P_Y with a Lebesgue density L^d-a.e. finiteness implies P-a.e. finiteness and 'S f_Y integrable' is P-integrability; for laws with atoms only the P-a.e. version gives the expectation a meaning
--   - generalization: ℝ^d (d ≥ 1 implicitly) → EuclideanSpace ℝ (Fin d) for every d : ℕ, including d = 0; reason: the d = 0 instance (a point) is extra and the statement specializes to the source for d ≥ 1
--   - encoding: h a nonnegative integrable Radon–Nikodym derivative of λ (Assumption 1(a)) → h measurable, h z ≥ 0 for every z, Integrable h; reason: a Radon–Nikodym derivative is Borel measurable and can be chosen pointwise nonnegative; the pointwise version matters for w = δ₀, where the score evaluates h(y) ((12), p. 15)
--   - encoding: (S′)Γ(A,y;w,h,α) = ∫ (α − w(z − y)) 1{z ∈ A} h(z) dz (11) → α ∫_A h − (µ_{y,w}(A)).toReal (levelSetScore), the split used by the paper in ∆′′ (p. 33); reason: the two agree whenever µ_{y,w}(A) < ∞; toReal returns 0 at ∞, and every theorem assumes the mass finite P-a.e.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, proof of Theorem 2 (ii), unnumbered, p. 34

import Mathlib
import Definitions.Def_LevelSetScores_weightedMass
import Definitions.Def_LevelSetScores_levelSetScore

open MeasureTheory
open scoped ENNReal

namespace LevelSetScores

/-- **`∆′ ≥ 0` with `{Ξ[Y] > α}` as the comparison set.**
Meng, Taylor, Ben Taieb, Li, *Scores for Multivariate Distributions and Level Sets*,
arXiv:2002.09578v6, proof of Theorem 2 (ii), unnumbered, p. 34: "Therefore, the integrand of
∆′ is pointwise non-negative, so ∆′ ≥ 0."

If `A` and `U = {Ξ > α}` are measurable with `P`-a.e. finite weighted mass and `P`-integrable
scores, then `E_P[S(U, ·)] ≤ E_P[S(A, ·)]`.

**Formalization Note.** The kernel `w` is the s-finite measure `ν`, `f_Y ∗ w` is a Lebesgue
density `Ξ` of `Measure.conv P ν`, and the score is `levelSetScore` (display (11)). No sign
condition on `Ξ` is needed: the inequality holds for every version of the density. -/
theorem delta_prime_nonneg {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [SFinite ν]
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]
    {Ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hΞ_meas : Measurable Ξ)
    (hΞ : Measure.conv P ν = volume.withDensity (fun z => ENNReal.ofReal (Ξ z)))
    {α : ℝ} (hα : 0 < α)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    (hA_fin : ∀ᵐ y ∂P, weightedMass h ν A y ≠ ∞)
    (hA_int : Integrable (levelSetScore h ν α A) P)
    (hU_fin : ∀ᵐ y ∂P, weightedMass h ν {z | α < Ξ z} y ≠ ∞)
    (hU_int : Integrable (levelSetScore h ν α {z | α < Ξ z}) P) :
    ∫ y, levelSetScore h ν α {z | α < Ξ z} y ∂P ≤ ∫ y, levelSetScore h ν α A y ∂P := by sorry

end LevelSetScores
