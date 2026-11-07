-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_19
-- name    : OMSRArbitrary.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:59.953521+00:00
-- url     : https://prove2.me/theorems/e961be1e-5928-4372-8502-838f9637583a
-- title:
--   Lemma 19 — $\mathbb E[M]\le g(u)\Pr[\mathrm{PG}(u)\text{ matches }i]$ implies (7) for $\gamma_\Lambda$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Let the weights lie within a factor $\Lambda\in[1,\infty]$ of each other and $c$ be integrable with $0\le c\le g$. Fix a resource $i$ and seeds $u=(u_k)$ in $[0,1]$, write $u=u_i$, and let expectations and probabilities be over the thresholds $z$ of the correlated model.
--
--   **Lemma 19.** If
--   $$\mathbb E[M]\ \le\ \tfrac1{r_i}\mathbb E[\theta_i]=g(u)\Pr[\mathrm{PG}(u)\text{ matches }i],$$
--   then (7) holds for the target $\gamma_\Lambda$, with $\pi_t=P_t^{-i}/(r_ip_{it})$, for every deterministic non-anticipative policy in the role of OPT.
--
--   It reduces the per-seed inequality to a comparison of the largest demand $M$ with the dual $\theta_i$.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: Λ ∈ [1, ∞] and weights within a factor Λ of each other; σ_Λ = σ/Λ → ρ = 1/Λ ∈ [0,1] with ρ r_j ≤ r_k for all j, k; σ_Λ = ρ σ; reason: ρ = 0 is Λ = ∞ and ρ = 1 is Λ = 1
--   - encoding: an integrable tradeoff function c : [0,1] → [0,1] with 0 ≤ c ≤ g → c : ℝ → ℝ, IntegrableOn c [0,1], 0 ≤ c x ≤ g x for x ∈ [0,1]; reason: c ≤ g ≤ 1 gives values in [0,1]; values outside [0,1] never enter
--   - encoding: E and Pr over the thresholds z with all seeds fixed (Sections 4–5, App. F) → integrals over z ∼ seedLaw m (i.i.d. uniform on [0,1]) at a fixed seed vector u ∈ [0,1]^n; reason: the correlated model draws z i.i.d. uniform on [0,1]
--   - encoding: hypothesis E[M] ≤ (1/r_i) E[θ_i] = g(u) Pr[PG(u) matches i] → hypothesis E[M] ≤ g(u_i) Pr[PG(u) matches i]; reason: the two right sides are equal by the definition of θ_i
--   - encoding: (7) for the target γ_Λ with π_t = P_t^{−i}/(r_i p_it) → PerSeedInequality with gammaW and piW (expectations as ∫⁻ of nonnegative integrands); reason: the same inequality; both sides are bounded and nonnegative
--   - generalization: OPT, an optimal non-anticipative policy, taken deterministic → every deterministic policy opt (run through the published legalize D false); reason: the argument uses only that OPT is a legal deterministic non-anticipative policy; the statement specializes to OPT
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 19, p.24 (restated and proved p.40)

import Mathlib
import Definitions.Def_OMSRArbitrary_Duals
import Definitions.Def_OMSRArbitrary_PerResource

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw DetPolicy unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 19** (arXiv:2611.03598, §5.1, p.24; restated and proved p.40): if
`E[M] ≤ (1/r_i) E[θ_i] = g(u) Pr[PG(u) matches i]`, then (7) holds for the target `γ_Λ`.

Seeds `u` are fixed (`u = u_i`), expectations are over the thresholds `z`, and (7) is the
per-seed inequality with the target `γ_Λ` and the paper's `π_t = P_t^{−i}/(r_i p_{it})`.

**Formalization Note.** The hypothesis is written in its second form `g(u) Pr[PG(u) matches i]`
(the equality with `(1/r_i)E[θ_i]` is the definition of `θ_i`). The conclusion is stated for every
deterministic policy in the role of OPT. -/
theorem lemma_19 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (c : ℝ → ℝ) (hc_int : IntegrableOn c (Set.Icc 0 1))
    (hc_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c x) (hc_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, c x ≤ g x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρr : ∀ j k, ρ * D.reward j ≤ D.reward k)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n)
    (hM : ∫ z, Mmax D g c ρ u i z ∂seedLaw m ≤ g (u i) * matchProb D g u i) :
    ∀ opt : DetPolicy n m,
      PerSeedInequality D g (gammaW g c ρ) (fun j v z t => piW D g v j z t) opt i u := by sorry

end OMSRArbitrary
