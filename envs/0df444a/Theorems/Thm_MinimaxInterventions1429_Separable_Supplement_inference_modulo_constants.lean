-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_inference_modulo_constants
-- name    : MinimaxInterventions1429.Separable.Supplement.inference_modulo_constants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:21:10.578827+00:00
-- url     : https://prove2.me/theorems/aa30ee67-a6e3-4962-ad47-07d77b3c3d6d
-- title:
--   Lemma 6.7 — Inference modulo constants
-- statement:
--   Fix a public group design, a nonempty row set $R$, an even individual set $S$ with $|S|\ge2$, and labels $y^0$. Let $\mathcal D$ agree with $y^0$ outside $S$ and have exactly $|S|/2$ ones on $S$. Take $\varepsilon\ge0$, $\delta\in[0,1)$ and $0\le\beta<\pi_{\varepsilon,\delta}$, and let $\varpi=\sqrt{(\pi_{\varepsilon,\delta}-\beta)/(1-\beta)}$. Any full-domain $(\varepsilon,\delta)$-DP vector release with centered error at most $\tau$ and success at least $1-\beta$ on every $y\in\mathcal D$ satisfies
--   $$\tau\ge\tfrac12\varpi\sigma_{R,S}(A)\sqrt{|S|/|R|}.$$
--   Privacy applies also to intermediate databases outside $\mathcal D$. Zero restricted singular values remain allowed. This is the inference lower bound used by the spectral threshold.
--
--   Differences from the source:
--   - encoding: the restricted unit sphere, centered error, and balanced databases → Finset restrictions, Euclidean square-root sums and half-oscillation centered error; reason: only the nonempty sphere with even |S| >= 2 is used; privacy is on the entire label domain
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 6.7, printed p.22 (PDF p.24)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Groups
set_option autoImplicit false
universe u_inference_modulo_constants

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem inference_modulo_constants
    {N m : ℕ} [NeZero m] (hm : 2 ≤ m) (d : GroupDesign N m)
    (R : Finset (Fin m)) (S : Finset (Fin N)) (hR : R.Nonempty)
    (hS : 2 ≤ S.card) (heven : Even S.card) (y₀ : Labels N)
    (ε δ β τ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (hβ : 0 ≤ β ∧ β < privacyPi ε δ)
    (law : Labels N → Measure (Fin m → ℝ))
    (hprob : ∀ y, IsProbabilityMeasure (law y))
    (hDP : DifferentiallyPrivate replacement ε δ law)
    (hacc : centeredAccurate d law β τ (balancedClass S y₀)) :
    (1/2)*varpi ε δ β*restrictedSigma d.matrix R S*
      Real.sqrt ((S.card : ℝ)/R.card) ≤ τ := by sorry

end MinimaxInterventions1429.Separable.Supplement
