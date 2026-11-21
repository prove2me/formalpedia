-- Prove2me | Theorems.Thm_MasulloGRH_horizontal_integral_tendsto_zero_of_slowGrowth_of_lowerBound
-- name    : MasulloGRH.horizontal_integral_tendsto_zero_of_slowGrowth_of_lowerBound
-- status  : Proved
-- author  : @koffie
-- created : 2026-11-21T00:10:40.976046+00:00
-- url     : https://prove2.me/theorems/5605bffb-b994-43fd-bb16-bfaf4dbf8005
-- title:
--   Lemma B.3.1.2, corrected — horizontal integrals vanish when $|T_k|\ge c|k|^\gamma$
-- statement:
--   **Corrected form of Lemma B.3.1.2.** Let $a<b$ and let $f$ be meromorphic on $\mathbb C_{(a,b)}$ with slow growth near its poles (Definition B.3.1.1), witnessed by $(T_k)_{k\in\mathbb Z}$. Assume in addition that the ordinates grow at least polynomially:
--
--   $$|T_k|\ \ge\ c\,|k|^{\gamma}\qquad(k\neq0)$$
--
--   for some $c,\gamma>0$. Let $\varepsilon>0$ and let $\Phi$ be holomorphic and uniformly Schwartz on $\mathbb C_{(a-\varepsilon,b+\varepsilon)}$. Then
--
--   $$\lim_{|k|\to\infty}\int_a^b|f(\sigma+iT_k)\,\Phi(\sigma+iT_k)|\,d\sigma=0.$$
--
--   Without the polynomial lower bound the statement is false: see the disproof of `MasulloGRH.horizontal_integral_tendsto_zero_of_slowGrowth`. The source's proof implicitly uses this bound, with exponents $\gamma,\delta$ that are never introduced.
--
--   **Formalization Note** Only the horizontal lines $\operatorname{Im}s=T_k$, $k\in\mathbb Z$, are controlled by Definition B.3.1.1. Since $k$ ranges over all of $\mathbb Z$, these lines cover both the upper and the lower sides of the contours whenever the $T_k$ take both signs. The lines $\operatorname{Im}s=-T_k$ of the original statement are therefore not included.
-- source:
--   Corrected version of A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Lemma B.3.1.2, pp. 604–605: adds the lower bound |T_k| ≥ c|k|^γ used implicitly in the proof (eq. (B.3.1.3)). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_MellinRpos
import Definitions.Def_MasulloGRH_SlowGrowthNearPoles

open Complex Filter Topology

namespace MasulloGRH

theorem horizontal_integral_tendsto_zero_of_slowGrowth_of_lowerBound (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ) (T : ℤ → ℝ) (hf : HasSlowGrowthNearPoles f a b T)
    (hT : ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧ ∀ k : ℤ, k ≠ 0 → c * |(k : ℝ)| ^ γ ≤ |T k|)
    (ε : ℝ) (hε : 0 < ε) (Φ : ℂ → ℂ)
    (hΦd : DifferentiableOn ℂ Φ (openStrip (a - ε) (b + ε)))
    (hΦ : UniformlySchwartzOnStrip Φ (a - ε) (b + ε)) :
    Tendsto (fun k : ℤ => ∫ σ in a..b,
        ‖f ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖) cofinite (𝓝 0) := by sorry

end MasulloGRH
