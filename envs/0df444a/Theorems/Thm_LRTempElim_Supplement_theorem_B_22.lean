-- Prove2me | Theorems.Thm_LRTempElim_Supplement_theorem_B_22
-- name    : LRTempElim.Supplement.theorem_B_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:39:15.902377+00:00
-- url     : https://prove2.me/theorems/0ef8bcd4-1b22-4509-a99d-f34909b2e0b0
-- title:
--   Theorem B.22 — final log-ratio error: $\epsilon_G\le\lambda/2$ gives $\hat G\succ0$, unique $\hat\theta=\hat G^{-1}\hat d$, (126) and (127)
-- statement:
--   Let $p,q$ be probability densities with respect to a σ-finite reference measure, with the same support up to a null set (Assumption B.2), and let $p_t=q^{1-t}p^t/Z_t$ be the geometric path (113). Assume $t\mapsto\log Z_t$ is continuously differentiable on $[0,1]$, the time score $s^\star$ is jointly measurable, and $\int_0^1\mathbb E_{P_t}[(s^\star)^2]\,dt$ and $\int_0^1\mathbb E_{P_t}[(\ell^\star)^2]\,dt$ are finite (Assumption B.3). Let $\phi:\mathcal X\to\mathbb R^m$ be a measurable feature map with $\int_0^1\mathbb E_{P_t}\|\phi\|_2^2\,dt<\infty$, the model well specified, $\ell^\star=\theta_*^\top\phi$ on the support, and $\Sigma_\nu=\mathbb E_\nu[\phi\phi^\top]$ finite for $\nu=(P+Q)/2$. Let $\lambda>0$ with $\lambda\le\lambda_{\min}(G)$ (in particular $\lambda=\lambda_{\min}(G)$ when $G$ is positive definite) and $\Lambda\ge\lambda_{\max}(\Sigma_\nu)$. For every $n\ge1$ and every $n$ groups of points defining $\hat G$ by (122) and $\hat d$, put $\epsilon_G=\|\hat G-G\|_{\mathrm{op}}$ and $\epsilon_d=\|\hat d-\vec d\|_2$. If $\epsilon_G\le\lambda/2$, then
--
--   1. $\hat G$ is positive definite;
--   2. $\hat\theta=\hat G^{-1}\hat d$ is the unique minimizer of $\hat L_n(\theta)=\theta^\top\hat G\theta-2\theta^\top\hat d$;
--   3. $$\|\hat\theta-\theta_*\|_2\le\frac2\lambda\big(\epsilon_d+\epsilon_G\|\theta_*\|_2\big); \tag{126}$$
--   4. $$R_{\log}=\mathbb E_\nu\big[(\hat\theta^\top\phi(X)-\theta_*^\top\phi(X))^2\big]\le\frac{4\Lambda}{\lambda^2}\big(\epsilon_d+\epsilon_G\|\theta_*\|_2\big)^2 . \tag{127}$$
--
--   Moment perturbations of the batch statistics thus control the parameter error and the final log-ratio error of the fixed-feature scalar estimator directly, through the query second-moment matrix.
--
--   **Formalization Note** The statement is deterministic in the batch points; the sampling law of Assumptions B.4–B.5 only produces them.
--
--   Differences from the source:
--   - generalization: λ = λ_min(G) and λ_max(Σ_ν) → any λ > 0 with λ∥v∥₂² ≤ v⊤Gv for all v, and any Λ with v⊤Σ_νv ≤ Λ∥v∥₂² for all v; reason: G and Σ_ν are symmetric, so λ = λ_min(G), Λ = λ_max(Σ_ν) satisfy these and give the source's statement
--   - generalization: "Under Assumption B.5" (exact geometric-path samples, independent groups) → every n ≥ 1 and every six families of points; reason: Theorem B.22 is deterministic; its conclusions do not use the sampling law
--   - generalization: densities on X ⊆ ℝᵈ, dx → densities on any measurable space with respect to a σ-finite reference measure; reason: only integrals against the reference measure are used
--   - generalization: Assumption B.3 "Differentiation under the integral and time integration by parts are valid" → not assumed; reason: not pinned down; Gθ∗ = d⃗ follows from the remaining hypotheses (q^{1−t}p^t ≤ p + q dominates the time derivative of E_{P_t}[f] for f ∈ L¹(ν), and µ(ℓ⋆) = log Z₁ − log Z₀ = 0)
--   - reading: "the query distribution ν" → ν = (P + Q)/2; reason: §2.2 fixes "Function risk is measured under ν = (P + Q)/2"
--   - encoding: "G is positive definite with λ > 0" (G implicitly finite) → ∫₀¹E_{P_t}[ϕ_j²] dt < ∞ for every j, plus the λ condition above; reason: G is defined only under this integrability
--   - encoding: Assumption B.2 "mutually absolutely continuous, with 0 < p, q < ∞ almost everywhere on their common support" → real-valued densities with {p > 0} = {q > 0} up to a null set; reason: the same condition for real densities
--   - encoding: "ℓ⋆ = θ∗⊤ϕ", "Σ_ν finite", "∫₀¹E_{P_t}[(s⋆)²], ∫₀¹E_{P_t}[(ℓ⋆)²] finite" → ℓ⋆ = θ∗⊤ϕ a.e. on {p > 0}; coordinates of ϕ in L²(ν); integrability on [0,1] × X; ϕ measurable; reason: Lean form of the stated conditions and the standing measurability of features
--   - encoding: "θ̂ is the unique empirical minimizer" → L̂_n(θ̂) ≤ L̂_n(θ) for all θ, with equality only at θ = θ̂; reason: definition of a unique minimizer
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), Theorem B.22, eqs. (126)–(127), p.38 (pdf p.40); Assumptions B.2–B.3, p.31 (pdf p.33); Assumption B.5, p.38; eqs. (120)–(122), pp.33–34 (pdf pp.35–36)

import Mathlib
import Definitions.Def_LRTempElim_Supplement_Norms
import Definitions.Def_LRTempElim_Supplement_GeometricPath

open MeasureTheory Matrix Set

namespace LRTempElim

namespace Supplement

/-- **Theorem B.22** (Final log-ratio error). Chen, Wu, Yang, Zeng, *Likelihood-Ratio Learning
under Weak Overlap via Analytic Temporal Elimination*, STOC 2027 submission (manuscript of
2026-11-03, sha256 eee65139…), Theorem B.22, eqs. (126)–(127), p.38 (pdf p.40), under
Assumptions B.2, B.3 (p.31, pdf p.33) and B.5 (p.38), with the batch statistics (120)–(122)
(pp.33–34, pdf pp.35–36).

"Under Assumption B.5, let ϵ_G = ∥Ĝ − G∥_op and ϵ_d = ∥d̂ − d⃗∥₂. If ϵ_G ≤ λ/2, then Ĝ is positive
definite, θ̂ = Ĝ⁻¹d̂ is the unique empirical minimizer, and ∥θ̂ − θ∗∥₂ ≤ (2/λ)(ϵ_d + ϵ_G∥θ∗∥₂). (126)
Consequently, for an independent query X ∼ ν,
R_log := E_ν[(θ̂⊤ϕ(X) − θ∗⊤ϕ(X))²] ≤ (4λ_max(Σ_ν)/λ²)(ϵ_d + ϵ_G∥θ∗∥₂)². (127)"

**Formalization Note.**
* Assumption B.2: `p`, `q` are probability densities with respect to a σ-finite
  reference measure `ρ`, with the same support up to a `ρ`-null set (mutual absolute continuity;
  real values are finite).
* Assumption B.3: geometric path (113) (`geomDens`); `t ↦ log Z_t` is `C¹` on `[0, 1]`; `s⋆` is
  jointly measurable; `∫₀¹ E_{P_t}[(s⋆)²] dt` and `∫₀¹ E_{P_t}[(ℓ⋆)²] dt` are finite (integrability
  on `[0, 1] × X`). Its sentence "Differentiation under the integral and time integration by parts
  are valid" is not assumed.
* Assumption B.5: `ℓ⋆ = θ∗⊤ϕ` `ρ`-a.e. on the support; `ϕ` measurable with
  `∫₀¹ E_{P_t}∥ϕ∥² dt < ∞` (so that `G` is defined); `ν = (P + Q)/2` with finite `Σ_ν`. Its
  sampling clauses (exact geometric-path samples, independent groups) only produce the points; the
  statement holds for every `n ≥ 1` and every six families of points defining `Ĝ` by (122) and `d̂`.
* `λ` is any positive number with `λ∥v∥₂² ≤ v⊤Gv` for all `v`, i.e. `0 < λ ≤ λ_min(G)` (`G` is
  symmetric); `Λ` is any number with `v⊤Σ_ν v ≤ Λ∥v∥₂²`, i.e. `Λ ≥ λ_max(Σ_ν)`. The paper's case is
  `λ = λ_min(G)`, `Λ = λ_max(Σ_ν)`.
* `ϵ_G` is the spectral norm (`opNorm`), `ϵ_d` and `∥θ∗∥₂` Euclidean (`eNorm`). `θ̂ = Ĝ⁻¹d̂` with
  `Matrix.inv`; "unique empirical minimizer" of `L̂ₙ(θ) = θ⊤Ĝθ − 2θ⊤d̂` is: `L̂ₙ(θ̂) ≤ L̂ₙ(θ)` for
  all `θ`, with equality only at `θ = θ̂`. -/
theorem theorem_B_22 {X : Type*} [MeasurableSpace X] (ρ : Measure X) [SigmaFinite ρ]
    (p q : X → ℝ) {m : ℕ} (ϕ : X → Fin m → ℝ) (θstar : Fin m → ℝ) (lam Λ : ℝ)
    -- Assumption B.2
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∫ x, p x ∂ρ = 1) (hq1 : ∫ x, q x ∂ρ = 1)
    (hsupp : ∀ᵐ x ∂ρ, (0 < p x ↔ 0 < q x))
    -- Assumption B.3
    (hZ : ContDiffOn ℝ 1 (fun t => Real.log (geomZ ρ p q t)) (Icc 0 1))
    (hs_meas : Measurable (fun z : ℝ × X => geomScore ρ p q z.1 z.2))
    (hs_L2 : Integrable (fun z : ℝ × X => geomDens ρ p q z.1 z.2 * geomScore ρ p q z.1 z.2 ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod ρ))
    (hℓ_L2 : Integrable (fun z : ℝ × X => geomDens ρ p q z.1 z.2 * logRatioD p q z.2 ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod ρ))
    -- Assumption B.5
    (hϕ : Measurable ϕ)
    (hwell : ∀ᵐ x ∂ρ, 0 < p x → logRatioD p q x = θstar ⬝ᵥ ϕ x)
    (hϕ_path : ∀ j, Integrable (fun z : ℝ × X => geomDens ρ p q z.1 z.2 * ϕ z.2 j ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod ρ))
    (hϕ_nu : ∀ j, Integrable (fun x => (p x + q x) / 2 * ϕ x j ^ 2) ρ)
    (hlam : 0 < lam) (hG : ∀ v : Fin m → ℝ, lam * eNorm v ^ 2 ≤ v ⬝ᵥ (matG ρ p q ϕ *ᵥ v))
    (hΛ : ∀ v : Fin m → ℝ, v ⬝ᵥ (sigmaNu ρ p q ϕ *ᵥ v) ≤ Λ * eNorm v ^ 2)
    -- the batch
    (n : ℕ) (hn : 1 ≤ n) (Xs Xs' Zs Ws Ps Qs : Fin n → X)
    (hεG : opNorm (batchG ϕ Xs Xs' Zs Ws - matG ρ p q ϕ) ≤ lam / 2) :
    (batchG ϕ Xs Xs' Zs Ws).PosDef ∧
    (∀ θ : Fin m → ℝ,
      batchRisk (batchG ϕ Xs Xs' Zs Ws) (batchD ϕ Ps Qs)
          ((batchG ϕ Xs Xs' Zs Ws)⁻¹ *ᵥ batchD ϕ Ps Qs) ≤
        batchRisk (batchG ϕ Xs Xs' Zs Ws) (batchD ϕ Ps Qs) θ ∧
      (batchRisk (batchG ϕ Xs Xs' Zs Ws) (batchD ϕ Ps Qs) θ =
          batchRisk (batchG ϕ Xs Xs' Zs Ws) (batchD ϕ Ps Qs)
            ((batchG ϕ Xs Xs' Zs Ws)⁻¹ *ᵥ batchD ϕ Ps Qs) →
        θ = (batchG ϕ Xs Xs' Zs Ws)⁻¹ *ᵥ batchD ϕ Ps Qs)) ∧
    eNorm ((batchG ϕ Xs Xs' Zs Ws)⁻¹ *ᵥ batchD ϕ Ps Qs - θstar) ≤
      2 / lam * (eNorm (batchD ϕ Ps Qs - vecD ρ p q ϕ) +
        opNorm (batchG ϕ Xs Xs' Zs Ws - matG ρ p q ϕ) * eNorm θstar) ∧
    riskLog ρ p q ϕ ((batchG ϕ Xs Xs' Zs Ws)⁻¹ *ᵥ batchD ϕ Ps Qs) θstar ≤
      4 * Λ / lam ^ 2 * (eNorm (batchD ϕ Ps Qs - vecD ρ p q ϕ) +
        opNorm (batchG ϕ Xs Xs' Zs Ws - matG ρ p q ϕ) * eNorm θstar) ^ 2 := by sorry

end Supplement

end LRTempElim
