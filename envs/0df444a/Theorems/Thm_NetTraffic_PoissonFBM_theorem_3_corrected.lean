-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_theorem_3_corrected
-- name    : NetTraffic.PoissonFBM.theorem_3_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:14.95288+00:00
-- url     : https://prove2.me/theorems/7d8390aa-0947-4a65-9c9e-3eefd3340019
-- title:
--   Theorem 3 (corrected σ²), p. 55 — under fast growth, (A(T·) − λμ_on T·)/[λT³F̄_on(T)σ²]^{1/2} → B_H in (𝔻[0,∞), J₁)
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$, $1<\alpha<2$, $L$ slowly varying, with mean $\mu_{\mathrm{on}}$. Let the connection rate $\lambda=\lambda(T)>0$ be non-decreasing in $T$ and satisfy the fast growth Condition 2, $b(\lambda T)/T\to\infty$. For each $T$ let $A$ be the cumulative input of the infinite source Poisson model with rate $\lambda(T)$. Then
--   $$\frac{A(T\,\cdot)-\lambda\mu_{\mathrm{on}}T(\cdot)}{[\lambda T^3\bar F_{\mathrm{on}}(T)\sigma^2]^{1/2}}\xrightarrow{d}B_H(\cdot)\quad\text{in }(\mathbb D[0,\infty),J_1),\qquad \sigma^2=\frac{2}{(\alpha-1)(2-\alpha)(3-\alpha)},$$
--   where $B_H$ is standard fractional Brownian motion with Hurst index $H=(3-\alpha)/2\in(1/2,1)$.
--
--   Under fast growth the cumulative input is approximated by a Gaussian, self-similar process with long-range dependent increments, in contrast to the stable Lévy limit with independent increments under slow growth (Theorem 1).
--
--   **Correction.** The paper states the theorem with $\sigma^2$ given by its (6.6), $\sigma^2=\frac1{3-\alpha}\big[\frac\alpha{2-\alpha}+\frac2{\mu_{\mathrm{on}}}\big]$. With that value the theorem is false: $\mathrm{Var}\,A(T)\sim\frac{2}{(\alpha-1)(2-\alpha)(3-\alpha)}\lambda T^3\bar F_{\mathrm{on}}(T)$ (from (2.14) and Karamata's theorem), so the normalised process would have a non-standard limit, while $\mathrm{Var}\,B_H(1)=1$. The proof's (6.4) omits the factor $\lambda m_2\sim\lambda m_3\sim\lambda\mu_{\mathrm{on}}$, and (6.2) drops the term $(P_4-EP_4)T$, which is not negligible under Condition 2. The statement here uses the corrected value.
--
--   **Formalization Note** Weak convergence is stated in coupling (Skorokhod representation) form: for every sequence $T_n\to\infty$ there is one probability space carrying processes $Y_n$ with the law of $G_{T_n}$ (laws on $\mathbb R^{[0,\infty)}$ with the product σ-algebra, i.e. all finite-dimensional distributions) and a standard fractional Brownian motion $Y'$ with $H=(3-\alpha)/2$, such that almost surely $Y_n\to Y'$ in $J_1$; $J_1$ convergence includes that every $Y_n$ and $Y'$ has càdlàg paths. On the Polish space $\mathbb D[0,\infty)$ this is equivalent to weak convergence. Because $t\mapsto A(Tt)$ and the limit have continuous paths, $J_1$ convergence here coincides with locally uniform convergence; $J_1$ is kept as printed.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 55, Theorem 3 (σ² of (6.6), p. 57, corrected, see description)

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- Theorem 3, p. 55, with the corrected `σ²`: under (2.8), `λ` non-decreasing and Condition 2,
`G_T(·) = (A(T·) - λμ_on T(·))/[λT³F̄_on(T)σ²]^{1/2}` with `σ² = 2/((α-1)(2-α)(3-α))` converges
weakly in `(𝔻[0, ∞), J₁)` to standard fractional Brownian motion `B_H`, `H = (3 - α)/2`.
Weak convergence is stated in coupling form: along every sequence `T_n → ∞` there are, on one
probability space, càdlàg copies `Y_n` of the laws of `G_{T_n}` and a standard FBM `Y'` with
`Y_n → Y'` in `J₁` almost surely. -/
theorem theorem_3_corrected
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, NetTraffic.PoissonStable.IsPoissonModel (P T) (lam T) Fon (Γ T) (X T))
    (hC2 : Condition2 Fon lam) :
    ∀ Tn : ℕ → ℝ, Tendsto Tn atTop atTop →
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (Y : ℕ → ℝ≥0 → Ω₀ → ℝ)
        (Y' : ℝ≥0 → Ω₀ → ℝ),
        IsProbabilityMeasure Q ∧
        (∀ n, Measurable (fun ω (t : ℝ≥0) => Y n t ω)) ∧
        (∀ n, Q.map (fun ω (t : ℝ≥0) => Y n t ω) =
          (P (Tn n)).map (fun ω (t : ℝ≥0) => G Fon α lam (Γ (Tn n)) (X (Tn n)) (Tn n) t ω)) ∧
        IsStdFBM (hurst α) Y' Q ∧
        ∀ᵐ ω ∂Q, SkorohodTendsto (fun n t => Y n t ω) (fun t => Y' t ω) := by sorry

end NetTraffic.PoissonFBM
