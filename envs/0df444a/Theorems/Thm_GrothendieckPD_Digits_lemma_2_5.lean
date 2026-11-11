-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_2_5
-- name    : GrothendieckPD.Digits.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:47.051268+00:00
-- url     : https://prove2.me/theorems/ecbbfe28-dca5-4451-acf3-34c3a8570ae4
-- title:
--   Lemma 2.5: $\sum_m|c_m(f,g)|\le1$; $H_{f,g}$, $H_\mu$ converge on $|t|\le1$, holomorphic on $|t|<1$
-- statement:
--   Let $f,g:\mathbb R^n\to\{\pm1\}$ be measurable and $c_m(f,g)=\langle\Pi_mf,\Pi_mg\rangle$ their Hermite coefficients under $\gamma_n$. Then
--   $$\sum_{m\ge0}|c_m(f,g)|\le1 .$$
--   For every distribution $\mu$ on pairs of such functions, also $\sum_m|c_m(\mu)|\le1$, with an explicitly summable series (p. 5, proof). Consequently $\mathcal C\subseteq\ell_1$. Moreover, for every such pair and for every distribution $\mu$ on pairs of measurable $\pm1$-valued functions, the power series
--   $$H_{f,g}(t)=\sum_m c_m(f,g)t^m,\qquad H_\mu(t)=\sum_m c_m(\mu)t^m$$
--   converge absolutely and uniformly for $t\in\mathbb C$, $|t|\le1$, and are holomorphic on $|t|<1$.
--
--   This is the analytic fact that makes the coefficient sequences of rounding schemes elements of $\ell_1$, the space on which the duality of Theorem 2.2 is set.
--
--   Differences from the source:
--   - encoding: c_m(f, g) = ⟨Π_m f, Π_m g⟩ → the moment sum ∑_{|α| = m} E[f He_α] E[g He_α] / α! (GrothendieckLB.pmInner); reason: same value by orthonormality of ψ_α = He_α/√α!
--   - reading: a distribution µ on pairs of functions → a jointly measurable random pair (F, G) over a probability space (Ω, µ) (GrothendieckLB.MixedScheme); reason: the source fixes no σ-algebra on a space of functions; the random-pair reading contains every finite mixture and makes ω ↦ c_m(F ω, G ω) measurable
--   - reading: odd functions f, g : ℝⁿ → {±1} → f(−x) = −f(x) for γₙ-almost every x; reason: pointwise oddness is impossible for ±1-valued functions (f(0) = −f(0)); a.e. oddness is the only satisfiable meaning and every Hermite coefficient depends only on the a.e. class
--   - encoding: the series converge absolutely and uniformly for t ∈ ℂ, |t| ≤ 1, and are holomorphic for |t| < 1 → for |t| ≤ 1 the series of norms is summable, the partial sums converge uniformly on the closed unit ball of ℂ to the tsum, and the tsum is complex-differentiable on the open unit ball; reason: the standard meaning of each clause
--   - encoding: the proof states ∑_m |c_m(µ)| ≤ 1 for a general distribution µ → explicit Summable and ∑' m, |schemeCoeff S m| ≤ 1 conjuncts for every MixedScheme; reason: retains the full norm bound requested by the brief; summability makes the infinite sum genuine
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 2.5, p. 5

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames
open MeasureTheory Filter

namespace GrothendieckPD.Digits

/-- Lemma 2.5 (p. 5). For measurable `f, g : ℝ^n → {±1}`, `∑_m |c_m(f,g)| ≤ 1`; hence `𝒞 ⊆ ℓ1`;
and for every distribution `µ` on pairs of measurable `±1`-valued functions,
`∑_m |c_m(µ)| ≤ 1`; for every such pair and distribution, the power series `H(t) = ∑_m c_m t^m` converges absolutely and uniformly on the closed
complex unit disc and is holomorphic on the open unit disc. -/
theorem lemma_2_5 :
    (∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ), GrothendieckLB.IsSignFn f → GrothendieckLB.IsSignFn g →
      Summable (fun m => |coeff m f g|) ∧ ∑' m, |coeff m f g| ≤ 1) ∧
    (∀ c ∈ CSet, Memℓp c 1) ∧
    (∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ), GrothendieckLB.IsSignFn f → GrothendieckLB.IsSignFn g →
      (∀ t : ℂ, ‖t‖ ≤ 1 → Summable fun m => ‖((coeff m f g : ℝ) : ℂ) * t ^ m‖) ∧
      TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, ((coeff m f g : ℝ) : ℂ) * t ^ m)
        (fun t => ∑' m, ((coeff m f g : ℝ) : ℂ) * t ^ m) atTop (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (fun t => ∑' m, ((coeff m f g : ℝ) : ℂ) * t ^ m) (Metric.ball 0 1)) ∧
    (∀ (n : ℕ) (S : GrothendieckLB.MixedScheme n),
      (Summable fun m => |schemeCoeff S m|) ∧ (∑' m, |schemeCoeff S m| ≤ 1) ∧
      (∀ t : ℂ, ‖t‖ ≤ 1 → Summable fun m => ‖((schemeCoeff S m : ℝ) : ℂ) * t ^ m‖) ∧
      TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, ((schemeCoeff S m : ℝ) : ℂ) * t ^ m)
        (fun t => ∑' m, ((schemeCoeff S m : ℝ) : ℂ) * t ^ m) atTop (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (fun t => ∑' m, ((schemeCoeff S m : ℝ) : ℂ) * t ^ m)
        (Metric.ball 0 1)) := by sorry

end GrothendieckPD.Digits
