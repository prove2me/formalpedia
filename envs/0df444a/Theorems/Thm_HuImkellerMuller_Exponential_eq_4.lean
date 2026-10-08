-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_eq_4
-- name    : HuImkellerMuller.Exponential.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:01.690494+00:00
-- url     : https://prove2.me/theorems/765f23c2-ef8a-494f-b346-55df04663472
-- title:
--   (4), p. 6 — min{|a| : a ∈ C_t(ω)} ≤ k₁ λ⊗P-a.e., and C_t(ω) is closed
-- statement:
--   Assume the standing market hypotheses (predictable, uniformly bounded $b$ and $\sigma$, $d\le m$, uniform ellipticity $KI_d\ge\sigma\sigma^{\mathrm{tr}}\ge\varepsilon I_d$), and let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed and nonempty, $C_t(\omega)=\tilde C\sigma_t(\omega)$. Then:
--
--   1. there is a constant $k_1\ge0$ with
--   $$\min\{|a| : a\in C_t(\omega)\}\le k_1\qquad\text{for }\lambda\otimes P\text{-a.e. }(t,\omega);$$
--   2. for $P$-a.e. $\omega$ and every $t\le T$, the set $C_t(\omega)$ is closed.
--
--   The constant $k_1$ enters the growth bound (9) of the driver, and closedness of $C_t$ is what makes the projection sets $\Pi_{C_t}$ nonempty.
--
--   **Formalization Note** "$\min\{|a|\}\le k_1$" is stated as "some $a\in C_t(\omega)$ has $|a|\le k_1$". The hypothesis $\tilde C\ne\emptyset$ is added (without it the minimum does not exist). The page states closedness "for every $(\omega,t)$"; it relies on the full rank of $\sigma_t(\omega)$, which the ellipticity hypothesis gives for $P$-a.e. $\omega$, so closedness is stated for $P$-a.e. $\omega$ and every $t\le T$.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, (4), p. 6

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_Market

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- (4), p. 6: there is a constant k₁ ≥ 0 with min{|a| : a ∈ C_t(ω)} ≤ k₁ for λ ⊗ P-a.e. (t, ω);
moreover C_t(ω) is closed (for P-a.e. ω and every t ≤ T). -/
theorem eq_4
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (hmkt : MarketHyp P 𝓕 T b σ)
    (Ct : Set (Fin d → ℝ)) (hCt : IsClosed Ct) (hne : Ct.Nonempty) :
    (∃ k₁ : ℝ, 0 ≤ k₁ ∧ ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
      ∃ a ∈ Cset Ct σ q.1.toNNReal q.2, ‖a‖ ≤ k₁) ∧
    ∀ᵐ ω ∂P, ∀ t ≤ T, IsClosed (Cset Ct σ t ω) := by sorry

end HuImkellerMuller.Exponential
