-- Prove2me | Theorems.Thm_NarrowDNF_Approx_theorem_3_5
-- name    : NarrowDNF.Approx.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:43.835309+00:00
-- url     : https://prove2.me/theorems/9b3a14bd-30e5-47b5-9455-605f42bbff23
-- title:
--   Theorem 3.5 — Controlled monotonicization
-- statement:
--   Let $0<p<1$, let $d$ be a nonnegative integer, and let $e,L\ge0$. Let $f$ be increasing, let $J$ have increasing activations, and let $h$ be $\mathcal F_J$-measurable. Assume $J_S\equiv0$ for $|S|>d$ and
--   $$\mathbb P_p[f\ne h]\le e,\qquad\Lambda_p(J)\le L.$$
--   For every $\tau>0$ there exist a coordinate subset $D$ and an increasing Boolean function $u$ such that, for these same $D,u$,
--   $$u\text{ is }\mathcal F_{J^D}\text{-measurable},\qquad\mathbb P_p[f\ne u]\le e+\tau,\qquad
--   \mathbb E_p|A_{J^D}(X)|\le(2-p)^dL(1+e/\tau).$$
--   Both zero error budget and zero load budget are included. This provides increasing adaptive approximators with simultaneous error and information-cost control.
--
--   Differences from the source:
--   - encoding: coordinates [n] and bits {0,1} → Fin n and Bool with pointwise false < true; reason: coordinate relabeling preserves all source instances
--   - encoding: product probabilities and expectations → published Bernoulli event sums and exact real finite weighted sums; reason: the finite product law is identical and every cost is integrable
--   - encoding: local activations and F_J-measurability → functions on S → Bool and constancy on equal dependent-pair atoms; reason: locality and precisely the recorded adaptive information are preserved
--   - encoding: nonnegative integer cutoffs → natural numbers; reason: the domains coincide, including zero
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Theorem 3.5, p. 8 (PDF p. 9)

import Definitions.Def_NarrowDNF_Approx_Activation

namespace NarrowDNF.Approx

theorem theorem_3_5 {n : ℕ} (p : ℝ) (d : ℕ) (e L : ℝ)
    (f : Cube n → Bool) (J : ActivationFamily n) (h : Cube n → Bool)
    (hp : 0 < p) (hp_one : p < 1) (he : 0 ≤ e) (hL : 0 ≤ L)
    (hf : Monotone f) (hJ : IncreasingActivations J) (hh : AdaptiveMeasurable J h)
    (hd : ArityLE J d) (herr : error p f h ≤ e) (hload : load p J ≤ L) :
    ∀ τ : ℝ, 0 < τ → ∃ (D : Finset (Fin n)) (u : Cube n → Bool),
      Monotone u ∧ AdaptiveMeasurable (force J D) u ∧ error p f u ≤ e + τ ∧
      activeCost p (force J D) ≤ (2 - p) ^ d * L * (1 + e / τ) := by sorry

end NarrowDNF.Approx
