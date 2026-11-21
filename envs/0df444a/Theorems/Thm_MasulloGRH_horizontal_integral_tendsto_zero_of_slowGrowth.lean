-- Prove2me | Theorems.Thm_MasulloGRH_horizontal_integral_tendsto_zero_of_slowGrowth
-- name    : MasulloGRH.horizontal_integral_tendsto_zero_of_slowGrowth
-- status  : Disproved
-- author  : @koffie
-- created : 2026-11-21T00:01:21.137195+00:00
-- url     : https://prove2.me/theorems/7eef46e9-1a41-4059-b6aa-a41dc8fe10b9
-- title:
--   Lemma B.3.1.2 — horizontal integrals of $f\Phi$ vanish along the slow-growth ordinates
-- statement:
--   Let $a<b$, let $f$ be meromorphic on $\mathbb C_{(a,b)}$ with slow growth near its poles (Definition B.3.1.1), witnessed by $(T_k)_{k\in\mathbb Z}$. Let $\varepsilon>0$ and let $\Phi$ be holomorphic and uniformly Schwartz on $\mathbb C_{(a-\varepsilon,b+\varepsilon)}$ (Definition B.2.2.1). Then the integrals of $|f\Phi|$ over the horizontal segments at heights $\mp T_k$ vanish asymptotically:
--
--   $$\lim_{|k|\to\infty}\int_{a-iT_k}^{b-iT_k}|f(s)\Phi(s)|\,|ds|=0=\lim_{|k|\to\infty}\int_{a+iT_k}^{b+iT_k}|f(s)\Phi(s)|\,|ds|.$$
--
--   This is the lemma that makes the horizontal sides of the rectangle contours vanish in the proof of the Asymptotic Residue Theorem B.3.2.1.
--
--   **Formalization Note** The segment integrals are real interval integrals $\int_a^b|f\Phi|(\sigma\mp iT_k)\,d\sigma$, and $|k|\to\infty$ is the cofinite filter on $\mathbb Z$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix B, Lemma B.3.1.2 and eq. (B.3.1.2), pp. 604–605; Definitions B.2.2.1 (p. 600) and B.3.1.1 (p. 604). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_MellinRpos
import Definitions.Def_MasulloGRH_SlowGrowthNearPoles

open Complex Filter Topology

namespace MasulloGRH

theorem horizontal_integral_tendsto_zero_of_slowGrowth (a b : ℝ) (hab : a < b) (f : ℂ → ℂ)
    (T : ℤ → ℝ) (hf : HasSlowGrowthNearPoles f a b T) (ε : ℝ) (hε : 0 < ε) (Φ : ℂ → ℂ)
    (hΦd : DifferentiableOn ℂ Φ (openStrip (a - ε) (b + ε)))
    (hΦ : UniformlySchwartzOnStrip Φ (a - ε) (b + ε)) :
    Tendsto (fun k : ℤ => ∫ σ in a..b,
        ‖f ((σ : ℂ) - (T k : ℂ) * I) * Φ ((σ : ℂ) - (T k : ℂ) * I)‖) cofinite (𝓝 0) ∧
    Tendsto (fun k : ℤ => ∫ σ in a..b,
        ‖f ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖) cofinite (𝓝 0) := by sorry

end MasulloGRH
