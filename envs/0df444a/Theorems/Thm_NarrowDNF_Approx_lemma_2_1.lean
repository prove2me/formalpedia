-- Prove2me | Theorems.Thm_NarrowDNF_Approx_lemma_2_1
-- name    : NarrowDNF.Approx.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:20.335932+00:00
-- url     : https://prove2.me/theorems/566b26f6-81ce-44f9-916c-eb669fdb3379
-- title:
--   Lemma 2.1 — Hatami’s construction with arity and load
-- statement:
--   Let $0<p\le1/2$, let $f:\{0,1\}^n\to\{0,1\}$ be arbitrary, and let $0<a\le1$. Set
--   $$C_f=\lceil I_p(f)\rceil,\qquad d=\lceil10^3C_f/a\rceil,\qquad L=\exp(10^{10}a^{-2}C_f^2).$$
--   There exist increasing local activations $J$ and a Boolean function $h$ such that
--   $$\mathbb P_p[f\ne h]\le a,\qquad h\text{ is }\mathcal F_J\text{-measurable},\qquad
--   \operatorname{arity}(J)\le d,\qquad\Lambda_p(J)\le L.$$
--   Here $I_p$ is total independent-resampling influence, arity counts the largest nonzero activation's coordinate set, and load counts overlaps with multiplicity. The target $f$ need not be increasing, nor is monotonicity of $h$ asserted. Zero influence and $a=1$ are included.
--
--   This supplies a quantitative adaptive approximation with controlled locality and load.
--
--   Differences from the source:
--   - encoding: coordinates [n] and bits {0,1} → Fin n and Bool with pointwise false < true; reason: coordinate relabeling preserves all source instances
--   - encoding: product probabilities and expectations → published Bernoulli event sums and exact real finite weighted sums; reason: the finite product law is identical and every cost is integrable
--   - encoding: local activations and F_J-measurability → functions on S → Bool and constancy on equal dependent-pair atoms; reason: locality and precisely the recorded adaptive information are preserved
--   - encoding: ceilings of nonnegative real quantities → natural ceilings, with a⁻² represented by (a⁻¹)²; reason: influence and cutoff expressions are nonnegative and a is positive, so these are the exact ceilings and powers
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Lemma 2.1, p. 4 (PDF p. 5); Appendix A, pp. 11–12 (PDF pp. 12–13)

import Definitions.Def_NarrowDNF_Approx_Activation

namespace NarrowDNF.Approx

theorem lemma_2_1 {n : ℕ} (p a : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (ha : 0 < a) (ha_one : a ≤ 1) :
    let C_f : ℕ := ⌈FriedgutCoalition.totalPInfl p f⌉₊
    let d : ℕ := ⌈(10 : ℝ) ^ 3 * (C_f : ℝ) / a⌉₊
    let L : ℝ := Real.exp ((10 : ℝ) ^ 10 * a⁻¹ ^ 2 * (C_f : ℝ) ^ 2)
    ∃ (J : ActivationFamily n) (h : Cube n → Bool),
      IncreasingActivations J ∧ error p f h ≤ a ∧ AdaptiveMeasurable J h ∧
      arity J ≤ d ∧ load p J ≤ L := by sorry

end NarrowDNF.Approx
