-- Prove2me | Theorems.Thm_LefebvreVariations_poisson_inequalities_rate_one_second_moment
-- name    : LefebvreVariations.poisson_inequalities_rate_one_second_moment
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:26:52.101819+00:00
-- url     : https://prove2.me/theorems/8c59d069-7905-41a6-8a99-b227fa14a8bf
-- title:
--   Lefebvre's variations: the Poisson moment and tail inequalities hold for rate 1 and second moments
-- statement:
--   Let $\mu$ be the Poisson law of rate $\lambda=1$ on $\mathbb{N}$, $\nu=\mu\otimes\mu$, and $q=2$. For all $u>0$ and $0<v<1$:
--   $$\mathbb{E}_\mu[X^2]\le 4\max(1,1),\qquad \mathbb{E}_\mu|X-1|^2\le 4^{2}\cdot 1,\qquad \mathbb{E}_\nu(2+X+Y)^2\le 8^2\cdot 2^2,$$
--   $$\mu\{x\ge 1+u\}\le \Bigl(\tfrac{e^{u}}{(1+u)^{1+u}}\Bigr),\qquad \mu\{x\le 1-v\}\le e^{-v^2/2},$$
--   and all the moments involved are finite.
--
--   The three moment bounds are comfortable (the actual values are $2$, $1$ and $18$), while the two tail bounds are the classical Chernoff bounds for the Poisson law.
--
--   **Formalization Note** The statement is the full conclusion of `WangRenyiEntropy.Noninteger.poisson_inequalities` (Lemma 2.4, all five inequalities with integrability as a conclusion) with the hypotheses `lam = 1` and `q = 2` added; `lam : ℝ≥0`, `q : ℕ`, and `u v : ℝ` with `0 < u`, `0 < v < 1` as in the parent. The measure is Mathlib's `poissonMeasure lam`. The conditional clause for `1 ≤ lam` is kept verbatim and applies since `lam = 1`.
--
--   **Why this is a variation.** Variation of the open platform problem WangRenyiEntropy.Noninteger.poisson_inequalities (Lemma 2.4, five Poisson moment and tail inequalities for all rates and orders). It fixes the first non-degenerate rate lambda=1 (where the central-moment clause applies) and order q=2, in the parent's own statement, leaving u and v quantified; it is literally the parent with lam=1 and q=2 substituted, so it is a consequence of the parent. Related open platform lemmas (SharedVehicleApprox.Pricing.Supplement.lemma_35, FournierGuillin.Conc.lemma_9) concern other Poisson tail bounds and are not duplicates.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: WangRenyiEntropy.Noninteger.poisson_inequalities (platform, Open), Lemma 2.4 of Qisheng Wang, STOC 2027 submission #447 (October 2026), as given in the parent's source field (not independently re-checked). Tail bounds are the standard Chernoff bounds for Poisson variables (e.g. Mitzenmacher-Upfal, Probability and Computing, Thms 5.4-5.5, cited from memory). Numerical check in python3 at lambda=1, q=2: E X^2 = 2 <= 4, E|X-1|^2 = 1 <= 16, E(2+X+Y)^2 = 18 <= 256; the upper tail bound was checked on 60000 values of u in (0,60] with no violation; the lower tail event {x <= 1-v} is {x=0} for 0<v<1, of probability e^-1 <= e^{-v^2/2}.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Lemma 2.4 of `WangRenyiEntropy.Noninteger.poisson_inequalities` (five Poisson moment and tail inequalities) at the
first non-degenerate rate `λ = 1` and moment order `q = 2`, for all `u > 0` and `0 < v < 1`.
Source: the Chernoff bounds for the Poisson law, e.g. Mitzenmacher–Upfal, *Probability and Computing*, Thm 5.4 and 5.5
(cited from memory); the moment bounds are elementary. -/
theorem poisson_inequalities_rate_one_second_moment (lam : ℝ≥0) (hlam : lam = 1) (q : ℕ) (hq : q = 2)
    (u v : ℝ) (hu : 0 < u) (hv0 : 0 < v) (hv1 : v < 1) :
    let μ := poissonMeasure lam
    let ν := μ.prod μ
    Integrable (fun x : ℕ => (x : ℝ) ^ q) μ ∧
    Integrable (fun x : ℕ => |(x : ℝ) - (lam : ℝ)| ^ q) μ ∧
    Integrable (fun xy : ℕ × ℕ => (1 + (xy.1 : ℝ) + xy.2 + (lam : ℝ)) ^ q) ν ∧
    (∫ x : ℕ, (x : ℝ) ^ q ∂μ) ≤ (q : ℝ) ^ q * max (lam : ℝ) ((lam : ℝ) ^ q) ∧
    ((1 : ℝ) ≤ lam → (∫ x : ℕ, |(x : ℝ) - (lam : ℝ)| ^ q ∂μ) ≤
      (2 * q : ℝ) ^ q * Real.rpow lam ((q : ℝ) / 2)) ∧
    (∫ xy : ℕ × ℕ, (1 + (xy.1 : ℝ) + xy.2 + (lam : ℝ)) ^ q ∂ν) ≤
      (4 * q : ℝ) ^ q * (1 + (lam : ℝ)) ^ q ∧
    μ {x : ℕ | (1 + u) * (lam : ℝ) ≤ x} ≤
      ENNReal.ofReal (Real.rpow (Real.exp u / Real.rpow (1 + u) (1 + u)) lam) ∧
    μ {x : ℕ | (x : ℝ) ≤ (1 - v) * (lam : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(v ^ 2) * lam / 2)) := by
  sorry

end LefebvreVariations
