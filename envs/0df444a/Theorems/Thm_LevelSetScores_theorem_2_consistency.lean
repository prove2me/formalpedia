-- Prove2me | Theorems.Thm_LevelSetScores_theorem_2_consistency
-- name    : LevelSetScores.theorem_2_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:14.438808+00:00
-- url     : https://prove2.me/theorems/a1e7709f-94e0-4fe8-983c-5659676729ab
-- title:
--   Theorem 2 (first claim): consistency of the level set score (11) for $L(f_Y * w;\alpha)$ (corrected: $f_Y * w$ read as a Lebesgue density of $P_Y * w$)
-- statement:
--   Throughout, $\mathbb R^d$ carries its Borel $\sigma$-algebra and Lebesgue measure. Let $h \ge 0$ be a measurable integrable function, $d\lambda(z) = h(z)\,dz$, let the kernel $w$ be an s-finite measure $\nu$ on $\mathbb R^d$, let $P$ be a probability measure on $\mathbb R^d$ (the law $P_Y$ of the observation $Y$), and let $\Xi$ be a measurable Lebesgue density of the convolution $P * \nu$ (the paper's $\Xi[Y] = f_Y * w$). For a Borel set $B$ and $y \in \mathbb R^d$ write $\mu_{y,w}(B) = \int \mathbb 1\{y+u \in B\}\, h(y+u)\, d\nu(u)$, i.e. $\int w(z-y)\mathbb 1\{z\in B\} h(z)\,dz$, and $S(B, y) = \alpha\lambda(B) - \mu_{y,w}(B)$ for the score (11).
--
--   Let $\alpha > 0$ and $L = L(\Xi;\alpha) = \{\Xi \ge \alpha\}$. Let $A \subseteq \mathbb R^d$ be a Borel set such that $\mu_{y,w}(A) < \infty$ for $P$-a.e. $y$ and $y \mapsto S(A,y)$ is $P$-integrable. Then $L$ minimizes the expected score against $A$:
--
--   1. either $\mathbb E_P[\mu_{Y,w}(L)] = \infty$, so that $\mathbb E_P[S(L,Y)] = -\infty$;
--   2. or $\mu_{y,w}(L) < \infty$ for $P$-a.e. $y$, $y \mapsto S(L,y)$ is $P$-integrable, and
--   $$\mathbb E_P\big[(S')^\Gamma(L(f_Y * w;\alpha), Y; w,h,\alpha)\big] \le \mathbb E_P\big[(S')^\Gamma(A, Y; w,h,\alpha)\big].$$
--
--   That is, the level set score (11) is a consistent scoring function for the $\alpha$ level set of the smoothed density $f_Y * w$. With $w = \delta_0$ this is consistency of the excess mass score (12) for density level sets; with the Heaviside kernel it is consistency of the CDF level set score (13), which for $d = 1$ recovers the quantile score.
--
--   **Formalization Note** The strict-consistency claim and the layer-cake identity of Theorem 2 are not part of this item. The paper's density $f_Y * w$ is taken to be any Lebesgue density $\Xi$ of the measure $P_Y * w$; when $P_Y$ is discrete and $w = \delta_0$ the printed claim with the probability mass function fails (see below).
--
--   Differences from the source:
--   - reading: f_Y ∗ w, the convolution of the generalized density f_Y (PDF, pmf or mixture) with w, used both as a local Borel measure (Assumption 1(a)) and as a function (Ξ[Y] := (f_Y ∗ w)(z), p. 33) → Ξ is any measurable Lebesgue density of the measure Measure.conv P ν (hypothesis hΞ); reason: for a function kernel w and every P this density is z ↦ ∫ w(z − s) dP_Y(s), the convolution of p. 6; null-set changes of Ξ change no expected score
--   - correction: f_Y ∗ w with f_Y the pmf of a discrete P_Y (p. 6, p. 10) → f_Y ∗ w is a Lebesgue density of P_Y ∗ w; laws for which P_Y ∗ w has no density are excluded by hΞ; reason: counterexample to the printed claim: d = 1, w = δ₀, P_Y = δ₀ (pmf 1{z = 0}), h the standard normal density, α = 2; then L(f_Y; 2) = ∅ with expected score 0, while A = {0} satisfies the hypotheses and has expected score −h(0) = −1/√(2π) < 0
--   - reading: hypotheses stated for A only; conclusion 'E_{P_Y}[l(A,•)] is minimized by L(f_Y ∗ w; α)' → no hypothesis on L = {Ξ ≥ α}; conclusion: either E_P[µ_{Y,w}(L)] = ∞, or µ_{y,w}(L) < ∞ P-a.e., the score of L is P-integrable and E_P[S(L,·)] ≤ E_P[S(A,·)]; reason: the first case is E_P[S(L,·)] = −∞ in the paper's arithmetic, where L is trivially a minimizer; the form adds no hypothesis on L and implies the variant with hypotheses for both A and L
--   - generalization: w a nonnegative local Borel measure (Assumption 1(a)) → ν any s-finite measure on ℝᵈ; w(z − y) is integrated as ∫ φ(y + u) dν(u); reason: locally finite Borel measures on ℝᵈ are s-finite and nonnegative; a function kernel w ≥ 0 is volume.withDensity w and δ₀ is dirac 0, so the source's kernels are instances
--   - generalization: P_Y in a convex class V^d of probability measures satisfying Assumption 1 → P any Borel probability measure on ℝᵈ (subject to hΞ); reason: the claim is about each P_Y separately; the class V^d plays no role in it
--   - generalization: (S′)Γ(A,•;w,h,α) finite L^d-a.e. and (S′)Γ(A,•;w,h,α) f_Y(•) integrable → µ_{y,w}(A) < ∞ for P-a.e. y, and y ↦ (S′)Γ(A,y;w,h,α) is P-integrable; reason: for P_Y with a Lebesgue density L^d-a.e. finiteness implies P-a.e. finiteness and 'S f_Y integrable' is P-integrability; for laws with atoms only the P-a.e. version gives the expectation a meaning
--   - generalization: ℝ^d (d ≥ 1 implicitly) → EuclideanSpace ℝ (Fin d) for every d : ℕ, including d = 0; reason: the d = 0 instance (a point) is extra and the statement specializes to the source for d ≥ 1
--   - encoding: h a nonnegative integrable Radon–Nikodym derivative of λ (Assumption 1(a)) → h measurable, h z ≥ 0 for every z, Integrable h; reason: a Radon–Nikodym derivative is Borel measurable and can be chosen pointwise nonnegative; the pointwise version matters for w = δ₀, where the score evaluates h(y) ((12), p. 15)
--   - encoding: (S′)Γ(A,y;w,h,α) = ∫ (α − w(z − y)) 1{z ∈ A} h(z) dz (11) → α ∫_A h − (µ_{y,w}(A)).toReal (levelSetScore), the split used by the paper in ∆′′ (p. 33); reason: the two agree whenever µ_{y,w}(A) < ∞; toReal returns 0 at ∞, and every theorem assumes the mass finite P-a.e.
--   - reading: Assumption 1(b), (c) (conditions under which the L² scores (2), (3) are finite) → not hypotheses; reason: they are implications about the scores of Theorem 1, not restrictions on V^d, h or w; the first claim of Theorem 2 does not use them
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, Theorem 2 (first claim), display (11), p. 13; consistency and level set (9), p. 12; Assumption 1(a), p. 32; proof pp. 33–34

import Mathlib
import Definitions.Def_LevelSetScores_levelSet
import Definitions.Def_LevelSetScores_weightedMass
import Definitions.Def_LevelSetScores_levelSetScore

open MeasureTheory
open scoped ENNReal

namespace LevelSetScores

/-- **Theorem 2 (first claim): the level set score (11) is consistent for `L(f_Y ∗ w; α)`.**
Meng, Taylor, Ben Taieb, Li, *Scores for Multivariate Distributions and Level Sets*,
arXiv:2002.09578v6, Theorem 2, p. 13: "Let Vd, h, and w satisfy Assumption 1 in the appendix,
and w is nonnegative. Let α > 0, and let A ⊆ Rd be an arbitrary Borel set. Suppose
(S′)Γ(A,•;w,h,α) is finite Ld-a.e. and (S′)Γ(A,•;w,h,α)fY(•) is integrable. Then the following
expression defines a consistent scoring function for the α level set L(fY ∗ w;α):
(S′)Γ(A,y;w,h,α) = ∫Rd (α − w(z − y)) 1{z ∈ A} h(z) dz. (11)"
Consistency (p. 12): "EPY[l(A,•;w)] is minimized by L(fY ∗ w;α)". Assumption 1(a) (p. 32): `h`
is a nonnegative integrable Lebesgue density of `λ`, `w` a local Borel measure.

Let `h ≥ 0` be measurable and integrable, `ν` an s-finite measure (the kernel `w`), `P` a
probability measure (the law `P_Y`) such that `P ∗ ν` has Lebesgue density `Ξ`, and `α > 0`. For
every measurable `A` whose weighted mass is `P`-a.e. finite and whose score is `P`-integrable,
the level set `L = {Ξ ≥ α}` minimizes the expected score against `A`: either
`E_P[µ_{Y,w}(L)] = ∞` (so `E_P[S(L, ·)] = −∞` in the paper's arithmetic), or the score of `L` has
`P`-a.e. finite mass, is `P`-integrable, and `E_P[S(L, ·)] ≤ E_P[S(A, ·)]`.

**Formalization Note.** The kernel `w` is the s-finite measure `ν` (a function kernel is
`volume.withDensity w`, `δ₀` is `Measure.dirac 0`). `f_Y ∗ w` is read as a Lebesgue density `Ξ`
of `Measure.conv P ν` (correction: with `w = δ₀` and a discrete `P_Y` whose pmf is used as
`f_Y`, the printed claim is false). The paper's "finite `L^d`-a.e." and "`S f_Y` integrable"
become `P`-a.e. finiteness of the weighted mass and `P`-integrability of the score. The paper does
not state hypotheses for `L`; instead the first disjunct covers the case `E_P[S(L,·)] = −∞`. The
strict-consistency and layer-cake claims of Theorem 2 are not part of this item. -/
theorem theorem_2_consistency {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [SFinite ν]
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]
    {Ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hΞ_meas : Measurable Ξ)
    (hΞ : Measure.conv P ν = volume.withDensity (fun z => ENNReal.ofReal (Ξ z)))
    {α : ℝ} (hα : 0 < α)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    (hA_fin : ∀ᵐ y ∂P, weightedMass h ν A y ≠ ∞)
    (hA_int : Integrable (levelSetScore h ν α A) P) :
    ∫⁻ y, weightedMass h ν (levelSet Ξ α) y ∂P = ∞ ∨
      ((∀ᵐ y ∂P, weightedMass h ν (levelSet Ξ α) y ≠ ∞) ∧
        Integrable (levelSetScore h ν α (levelSet Ξ α)) P ∧
        ∫ y, levelSetScore h ν α (levelSet Ξ α) y ∂P ≤ ∫ y, levelSetScore h ν α A y ∂P) := by sorry

end LevelSetScores
