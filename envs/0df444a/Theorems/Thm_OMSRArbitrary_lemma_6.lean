-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_6
-- name    : OMSRArbitrary.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:02.221577+00:00
-- url     : https://prove2.me/theorems/94c398a9-1aef-40c1-b860-4e9c9f9583b7
-- title:
--   Lemma 6 — the per-seed inequality (7) and $\int_0^1\gamma(x,\pi)\,dx\ge\alpha$ give $\mathbb E[\mathrm{PG}]\ge\alpha\,\mathbb E[\mathrm{OPT}]$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$.
--   Let $\gamma(x,\pi)\ge0$ ($x\in[0,1]$, $\pi\ge0$) be a target and, for each resource $i$ and each arrival $t$ with an edge to $i$, let $\pi_t\ge0$ be a number determined by the seeds and the thresholds that does not depend on the seed $u_i$.
--
--   **Lemma 6.** Suppose that for every $i$, every $u$ and every $u_{-i}$
--   $$\mathbb E\Big[\sum_{t\in O_i}\lambda_t+\theta_i\,\Big|\,u_i=u,u_{-i}\Big]\ \ge\ r_i\,\mathbb E\Big[\sum_{t\in O_i}\mathbf 1\{z_t\le p_{it}\}\,\gamma(u,\pi_t)\,\Big|\,u_i=u,u_{-i}\Big],\tag{7}$$
--   where the expectations are over $z$. If, in addition, $\int_0^1\gamma(x,\pi)\,dx\ge\alpha$ for all $\pi\ge0$, then $\mathbb E[\mathrm{PG}]\ge\alpha\,\mathbb E[\mathrm{OPT}]$.
--
--   Integrating (7) over the seed of $i$ yields (6) of Lemma 5; the target then only has to integrate to $\alpha$.
--
--   **Formalization Note** OPT is any deterministic policy; $\gamma$ and $\pi_t$ are measurable; the expectations of (7) and the integral of $\gamma$ take values in $[0,\infty]$; $\mathbb E[\mathrm{PG}]$, $\mathbb E[\mathrm{OPT}]$ are correlated-model values.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - generalization: OPT, an optimal non-anticipative policy, taken deterministic → every deterministic policy opt (run through the published legalize D false); reason: the argument uses only that OPT is a legal deterministic non-anticipative policy; the statement specializes to OPT
--   - encoding: a target function γ(x, π) ≥ 0 and numbers π_t ≥ 0 (no regularity stated) → γ jointly Borel measurable, π_t jointly Borel measurable in (u, z); reason: the standing measurability convention under which the expectations in (7) are defined
--   - encoding: γ(x, π) ≥ 0 for x ∈ [0,1], π ≥ 0; π_t defined for arrivals t with an edge to i → γ ≥ 0 on [0,1] × [0,∞) and π_t ≥ 0 at arrivals with (i, t) ∈ E; reason: exactly the domains on which the source defines them
--   - encoding: the expectations in (7) and ∫₀¹ γ(x, π) dx → Lebesgue integrals ∫⁻ with values in [0, ∞] of the nonnegative integrands; reason: a generic γ may have infinite integrals; the extended values are the source values
--   - generalization: (7) for every u and every u_{−i} → (7) for every seed vector in [0,1]^n; reason: a weaker hypothesis: seeds lie in [0,1]^n; it specializes to the source statement
--   - encoding: E[PG] and E[OPT] (the correlated model is used from p.11 on) → pgValueCorr and optValueCorr, iterated integrals over u ∼ seedLaw n and z ∼ seedLaw m; reason: seeds and thresholds are independent uniforms (pp.11, 13); Lemma 2 equates the two models
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 6, eq. (7), p.14

import Mathlib
import Definitions.Def_OMSRArbitrary_Duals

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw DetPolicy unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 6** (arXiv:2611.03598, §3.1, p.14), reduction to the per-seed inequality: suppose that
for every `i`, every `u` and every `u_{−i}` the per-seed inequality (7) holds for a target `γ`
and numbers `π_t` independent of `u = u_i`; if in addition `∫₀¹ γ(x, π) dx ≥ α` for all `π ≥ 0`,
then `E[PG] ≥ α E[OPT]`.

**Formalization Note.** `γ` and `π_t` are generic, as in the paper: `γ(x, π) ≥ 0` for
`x ∈ [0,1]`, `π ≥ 0`, and `π_t = πt i u z t ≥ 0` at arrivals with an edge to `i`, not depending on
the seed `u_i`. Their measurability is the standing convention that makes the expectations
meaningful. The integral of `γ(·, π)` is a Lebesgue integral with values in `[0, ∞]`. OPT is any
deterministic policy `opt`; `E[PG]`, `E[OPT]` are correlated-model values (Lemma 2). (7) is
required at every seed vector in `[0,1]^n`. -/
theorem lemma_6 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (γ : ℝ → ℝ → ℝ) (hγ_meas : Measurable (Function.uncurry γ))
    (hγ_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ π : ℝ, 0 ≤ π → 0 ≤ γ x π)
    (πt : Fin n → Seeds n → Seeds m → Fin m → ℝ)
    (hπ_meas : ∀ i t, Measurable (fun p : Seeds n × Seeds m => πt i p.1 p.2 t))
    (hπ_nonneg : ∀ i u z t, (i, t) ∈ D.edges → 0 ≤ πt i u z t)
    (hπ_indep : ∀ i u z t (x : ℝ), πt i (Function.update u i x) z t = πt i u z t)
    (opt : DetPolicy n m) (α : ℝ)
    (h7 : ∀ (i : Fin n) (u : Seeds n), unitSeeds u → PerSeedInequality D g γ πt opt i u)
    (hγα : ∀ π : ℝ, 0 ≤ π →
      ENNReal.ofReal α ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (γ x π)) :
    α * optValueCorr D opt ≤ pgValueCorr D g := by sorry

end OMSRArbitrary
