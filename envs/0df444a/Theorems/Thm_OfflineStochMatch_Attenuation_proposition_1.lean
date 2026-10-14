-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_proposition_1
-- name    : OfflineStochMatch.Attenuation.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:06.668513+00:00
-- url     : https://prove2.me/theorems/1f3306ff-7ab4-4613-a978-8d9963212162
-- title:
--   Proposition 1, p. 14 — ∫₀¹ λφ ≥ λ(z*)∫₀¹ φ for λ ≥ 0 non-increasing and φ changing sign once at z*
-- statement:
--   Let $\lambda, \varphi : [0,1] \to \mathbb R$ be integrable, with $\lambda \ge 0$ and $\lambda$ non-increasing. Suppose there is $z^* \in [0,1]$ such that $\varphi(z) \ge 0$ for all $z \in [0, z^*]$ and $\varphi(z) \le 0$ for all $z \in [z^*, 1]$. Then
--   $$\int_0^1 \lambda(z)\varphi(z)\,dz \;\ge\; \lambda(z^*) \int_0^1 \varphi(z)\,dz.$$
--
--   In the paper this elementary bound drives the exchange argument (Lemma 6) for the case of patience $2$.
--
--   **Formalization Note** Integrability is interval integrability on $[0,1]$ with respect to Lebesgue measure; the monotonicity, sign and nonnegativity conditions are imposed on $[0,1]$ only. Under these hypotheses $\lambda\varphi$ is integrable on $[0,1]$ ($\lambda$ is bounded by $\lambda(0)$ there and monotone), so neither integral takes a default value.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 14, Proposition 1 (Proposition 11 of reference [33])

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem proposition_1 (lam φ : ℝ → ℝ)
    (hlam : IntervalIntegrable lam MeasureTheory.volume 0 1)
    (hφ : IntervalIntegrable φ MeasureTheory.volume 0 1)
    (hlam_nonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam z)
    (hlam_anti : AntitoneOn lam (Set.Icc (0 : ℝ) 1))
    (zs : ℝ) (hzs : zs ∈ Set.Icc (0 : ℝ) 1)
    (hφ_pos : ∀ z ∈ Set.Icc (0 : ℝ) zs, 0 ≤ φ z)
    (hφ_neg : ∀ z ∈ Set.Icc zs 1, φ z ≤ 0) :
    lam zs * ∫ z in (0 : ℝ)..1, φ z ≤ ∫ z in (0 : ℝ)..1, lam z * φ z := by sorry

end OfflineStochMatch.Attenuation
