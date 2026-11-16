-- Prove2me | Theorems.Thm_LRTempElim_Supplement_theorem_1
-- name    : LRTempElim.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:37:52.417173+00:00
-- url     : https://prove2.me/theorems/24098d6d-5800-4aab-bb27-6b48191853d5
-- title:
--   Theorem 1 — analytic elimination: $F(\theta)=(\theta-m)^\top A^{-1}(\theta-m)-\mathcal E$, Pythagorean form, minimizer $m$, and absolute calibration
-- statement:
--   Let $(P_t)_{t\in[0,1]}$ be a path of probability laws with densities $p_t$ with respect to a reference measure $\rho$, positive on a common support $S$ and zero off it, with $Q=P_0$, $P=P_1$ and $\ell^\star=\log(p/q)$. Assume that for $\rho$-a.e. $x\in S$ the map $t\mapsto\log p_t(x)$ is absolutely continuous on $[0,1]$, and that $C=\int_0^1\mathbb E_{P_t}[(s^\star_t)^2]\,dt<\infty$. Fix a measurable feature map $\phi:\mathcal X\to\mathbb R^k$ that is in $L^2(P_t)$ for a.e. $t$, and let $M,b,A,m,\mathcal E,J,F,\Pi_t$ be as in the definition of continuous elimination. Suppose $M(t)$ is positive definite for almost every $t$, the integrals defining $A$, $m$ and $\mathcal E$ are finite, and $A$ is positive definite. Then:
--
--   1. for every $\theta$, the constrained infimum of (3) is
--   $$
--   F(\theta)=(\theta-m)^\top A^{-1}(\theta-m)-\mathcal E; \tag{4}
--   $$
--   2. if $\Pi_t$ is the $L^2(P_t)$ projection onto the feature span (for a.e. $t$), then for every $\theta$
--   $$
--   F(\theta)+C=(\theta-m)^\top A^{-1}(\theta-m)+\int_0^1\|s^\star_t-\Pi_ts^\star_t\|^2_{L^2(P_t)}\,dt; \tag{5}
--   $$
--   3. the minimizer of $F$ is $\theta=m$, and it is the only one;
--   4. if $\log p_t-\log q=\phi^\top\eta(t)$ on $S$ for every $t\in[0,1]$, with $\eta$ absolutely continuous and $\eta(0)=0$, then $f_m=\phi^\top m=\ell^\star$ a.e. on $S$;
--   5. in general, a.e. on $S$,
--   $$
--   f_m-\ell^\star=\int_0^1(\Pi_t-I)s^\star_t\,dt; \tag{6}
--   $$
--   6. hence absolute calibration $f_m=\ell^\star$ (a.e. on $S$) holds exactly when this integrated residual vanishes (a.e. on $S$).
--
--   The theorem identifies the population target of analytic temporal elimination: eliminating the temporal coefficients leaves a static quadratic objective whose minimizer is the integrated moment readout $m$, and the representation error of that readout is exactly the integrated projection residual of the time score.
--
--   **Formalization Note** The admissible class of (3) is parameterized by $u=a'$ (integrable, $\int_0^1u=\theta$, finite energy). (4) is stated as: the value is the greatest lower bound of the set of values of $J$. $\Pi_ts^\star_t=\phi^\top c(t)$, and clauses 2, 5, 6 hold for every such family $c$.
--
--   Differences from the source:
--   - generalization: densities on $\mathcal X\subseteq\mathbb R^d$ with respect to a common reference measure → densities on any measurable space with respect to a reference measure ρ; reason: only integrals against ρ are used; ℝᵈ with Lebesgue measure is a special case
--   - generalization: ϕ_ζ with a constant feature → any measurable ϕ, no constant feature required; reason: no clause uses the constant feature; feature maps containing one are a special case
--   - generalization: §2.2 "differentiation and integration below are valid" → not assumed; reason: the phrase is not pinned down; the endpoint identity (2) follows from absolute continuity of t ↦ log p_t(x), and b is taken in the form E_{P_t}[ϕ s⋆_t]
--   - reading: b(t) = d/dt E_{P_t}[ϕ] = E_{P_t}[ϕ s⋆_t] → b(t) = E_{P_t}[ϕ s⋆_t]; reason: the paper gives both forms; their equality is exactly the interchange not assumed
--   - reading: "log p_t − log q = ϕ⊤η(t)", "f = ℓ⋆", (6) → for every t ∈ [0,1], ρ-a.e. on S; ρ-a.e. on S; ρ-a.e. on S; reason: densities are determined up to null sets
--   - encoding: "M(t) is positive definite almost everywhere" → for Lebesgue-a.e. t ∈ [0,1], with ϕ ∈ L²(P_t) for a.e. t; reason: M(t) is defined only when ϕ ∈ L²(P_t)
--   - encoding: "these integrals are finite" and C < ∞ → the entries of M⁻¹, the coordinates of M⁻¹b and b⊤M⁻¹b are integrable on [0,1]; for a.e. t ∈ [0,1], x ↦ p_t(x)s⋆_t(x)² is integrable and t ↦ E_{P_t}[(s⋆_t)²] is integrable on [0,1] (the iterated integral; no joint measurability); reason: finiteness of an integral is integrability in Lean
--   - encoding: the constrained infimum of (3) over a with a(0) = 0, a(1) = θ → infimum over u = a′ integrable with ∫₀¹u = θ and finite energy, stated as a greatest lower bound; reason: a ↦ a′ is a bijection between absolutely continuous a with a(0) = 0, a(1) = θ and integrable u with ∫u = θ; paths of infinite energy have J = +∞
--   - encoding: Π_t, the L²(P_t) projection → any c(t) with s⋆_t − ϕ⊤c(t) ∈ L²(P_t) orthogonal to every ϕ_j (a.e. t), clauses stated for every such c; reason: this characterizes the orthogonal projection
--   - encoding: "the minimizer is θ = m" → F(m) ≤ F(θ) for all θ, with equality only at θ = m; reason: "the minimizer" asserts a unique one
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), Theorem 1, eqs. (4)–(6), p.5 (pdf p.7); setting §2.2 eq. (2), p.4 (pdf p.6) and §3.1 eq. (3), p.5

import Mathlib
import Definitions.Def_LRTempElim_Supplement_Elimination

open MeasureTheory Matrix Set

namespace LRTempElim

namespace Supplement

/-- **Theorem 1** (Analytic elimination and absolute calibration). Chen, Wu, Yang, Zeng,
*Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027
submission (manuscript of 2026-11-03, sha256 eee65139…), Theorem 1, p.5 (pdf p.7), with the setting
of §2.2 (p.4, pdf p.6) and §3.1 (p.5).

"Suppose M(t) is positive definite almost everywhere. Define A = ∫₀¹ M(t)⁻¹ dt,
m = ∫₀¹ M(t)⁻¹b(t) dt, and E = ∫₀¹ b(t)⊤M(t)⁻¹b(t) dt. Assume these integrals are finite and A is
positive definite. Then the constrained infimum of (3) is F(θ, ζ) = (θ − m)⊤A⁻¹(θ − m) − E. (4)
If Π_{t,ζ} is the L²(P_t) projection onto the feature span, then
F + C = (θ − m)⊤A⁻¹(θ − m) + ∫₀¹ ∥s⋆_t − Π_{t,ζ}s⋆_t∥²_{L²(P_t)} dt. (5) For fixed features the
minimizer is θ = m. If log p_t − log q = ϕ⊤η(t) with absolutely continuous η and η(0) = 0, this
minimizer gives f = ℓ⋆. More generally, f_{m,ζ} − ℓ⋆ = ∫₀¹ (Π_{t,ζ} − I)s⋆_t dt. (6) Thus absolute
calibration holds exactly when this integrated residual vanishes."

**Formalization Note.**
* Path (§2.2, §3.1): densities `pt t` of `P_t` with respect to a reference measure `ρ`,
  each a probability density for `t ∈ [0, 1]` (integral `1`), positive on a
  common support `S` and zero off it; `Q = P₀`, `P = P₁`. For `ρ`-a.e. `x ∈ S`,
  `t ↦ log p_t(x)` is absolutely continuous on `[0, 1]`. The path-score energy
  `C = ∫₀¹ E_{P_t}[(s⋆_t)²] dt` is finite: for a.e. `t ∈ [0, 1]` the inner integral
  `E_{P_t}[(s⋆_t)²]` is finite (integrability in `x`), and `t ↦ E_{P_t}[(s⋆_t)²]` is integrable
  on `[0, 1]` (the iterated integral of the page; no joint measurability is assumed).
* The fixed feature map `ϕ` is measurable and in `L²(P_t)` for a.e. `t`, so that `M(t)` is defined.
  No constant feature is required.
* "these integrals are finite": the entries of `t ↦ M(t)⁻¹`, the coordinates of `t ↦ M(t)⁻¹b(t)`
  and `t ↦ b(t)⊤M(t)⁻¹b(t)` are integrable on `[0, 1]`.
* (4) is stated as: the value is the greatest lower bound of `J` over the admissible class
  (`objJValues`), so the infimum is attained as a genuine infimum, not a junk `sInf`.
* `Π_t s⋆_t = ϕ⊤c(t)` for any family `c` with `IsProjCoeff` at almost every `t`; (5), (6) and the
  calibration equivalence are stated for every such family.
* "the minimizer is θ = m": `F(m) ≤ F(θ)` for all `θ`, with equality only at `θ = m`.
* `f = ℓ⋆`, (6) and calibration are `ρ`-a.e. statements on the support `S`;
  `ℓ⋆ = log p₁ − log p₀ = log(p/q)`.
* The phrase "differentiation and integration below are valid" (§2.2) is not assumed; `b(t)` is
  the form `E_{P_t}[ϕ s⋆_t]`. -/
theorem theorem_1 {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    (pt : ℝ → X → ℝ) (S : Set X) {k : ℕ} (ϕ : X → Fin k → ℝ)
    (hpt_one : ∀ t ∈ Icc (0 : ℝ) 1, ∫ x, pt t x ∂ρ = 1)
    (hpt_pos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S, 0 < pt t x)
    (hpt_zero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∉ S, pt t x = 0)
    (hAC : ∀ᵐ x ∂ρ, x ∈ S → AbsolutelyContinuousOnInterval (fun t => Real.log (pt t x)) 0 1)
    (hC : (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
        Integrable (fun x => pt t x * timeScore pt t x ^ 2) ρ) ∧
      IntervalIntegrable (fun t => ∫ x, pt t x * timeScore pt t x ^ 2 ∂ρ) volume 0 1)
    (hϕ : Measurable ϕ)
    (hϕL2 : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∀ i, Integrable (fun x => pt t x * ϕ x i ^ 2) ρ)
    (hM : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), (momentM ρ pt ϕ t).PosDef)
    (hA : ∀ i j, IntervalIntegrable (fun t => (momentM ρ pt ϕ t)⁻¹ i j) volume 0 1)
    (hm : ∀ i, IntervalIntegrable
      (fun t => ((momentM ρ pt ϕ t)⁻¹ *ᵥ scoreB ρ pt ϕ t) i) volume 0 1)
    (hE : IntervalIntegrable
      (fun t => scoreB ρ pt ϕ t ⬝ᵥ ((momentM ρ pt ϕ t)⁻¹ *ᵥ scoreB ρ pt ϕ t)) volume 0 1)
    (hApd : (elimA ρ pt ϕ).PosDef) :
    -- (4): the constrained infimum of (3)
    (∀ θ : Fin k → ℝ, IsGLB (objJValues ρ pt ϕ θ)
      ((θ - elimM ρ pt ϕ) ⬝ᵥ ((elimA ρ pt ϕ)⁻¹ *ᵥ (θ - elimM ρ pt ϕ)) - elimE ρ pt ϕ)) ∧
    -- (5): the Pythagorean form, for the L²(P_t) projection Π_t s⋆_t = ϕ⊤c(t)
    (∀ c : ℝ → Fin k → ℝ,
      (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), IsProjCoeff ρ pt ϕ t (c t)) →
      ∀ θ : Fin k → ℝ, reducedF ρ pt ϕ θ + scoreEnergy ρ pt =
        (θ - elimM ρ pt ϕ) ⬝ᵥ ((elimA ρ pt ϕ)⁻¹ *ᵥ (θ - elimM ρ pt ϕ)) +
          ∫ t in (0 : ℝ)..1, projResidualSq ρ pt ϕ t (c t)) ∧
    -- the minimizer of F is θ = m (and it is the only one)
    (∀ θ : Fin k → ℝ, reducedF ρ pt ϕ (elimM ρ pt ϕ) ≤ reducedF ρ pt ϕ θ ∧
      (reducedF ρ pt ϕ θ = reducedF ρ pt ϕ (elimM ρ pt ϕ) → θ = elimM ρ pt ϕ)) ∧
    -- path closure gives f = ℓ⋆
    (∀ η : ℝ → Fin k → ℝ, (∀ i, AbsolutelyContinuousOnInterval (fun t => η t i) 0 1) →
      η 0 = 0 →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ x ∂ρ, x ∈ S →
        Real.log (pt t x) - Real.log (pt 0 x) = ϕ x ⬝ᵥ η t) →
      ∀ᵐ x ∂ρ, x ∈ S → ϕ x ⬝ᵥ elimM ρ pt ϕ = logRatio pt x) ∧
    -- (6) and: absolute calibration holds exactly when the integrated residual vanishes
    (∀ c : ℝ → Fin k → ℝ,
      (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), IsProjCoeff ρ pt ϕ t (c t)) →
      (∀ᵐ x ∂ρ, x ∈ S → ϕ x ⬝ᵥ elimM ρ pt ϕ - logRatio pt x =
        ∫ t in (0 : ℝ)..1, (ϕ x ⬝ᵥ c t - timeScore pt t x)) ∧
      ((∀ᵐ x ∂ρ, x ∈ S → ϕ x ⬝ᵥ elimM ρ pt ϕ = logRatio pt x) ↔
        (∀ᵐ x ∂ρ, x ∈ S → ∫ t in (0 : ℝ)..1, (ϕ x ⬝ᵥ c t - timeScore pt t x) = 0))) := by sorry

end Supplement

end LRTempElim
