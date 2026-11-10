-- Prove2me | Theorems.Thm_OptRobustCD_theorem_3_7
-- name    : OptRobustCD.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:10.639059+00:00
-- url     : https://prove2.me/theorems/1b405d02-9820-4762-8267-f71e67ac7e72
-- title:
--   Theorem 3.7 — tree characterization of optimal recovery [MNS16a, YP24], both directions
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, let $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$, and let $\mathrm{OPT}_{d,\lambda}=\lim_t\mathbb E|M_t|$ be the tree quantity of §3.3.
--
--   1. For every estimator $\hat\sigma(G)$ and every $\varepsilon>0$,
--   $$\Pr\bigl(\mathrm{ov}(\hat\sigma,\sigma^\star)>\mathrm{OPT}_{d,\lambda}+\varepsilon\bigr)\longrightarrow0.$$
--   2. Conversely, for every $\varepsilon>0$ there is an estimator, computable in time $n^{1+o(1)}$, whose overlap is at least $\mathrm{OPT}_{d,\lambda}-\varepsilon$ with high probability.
--
--   The first direction is [MNS16a, Theorem 2.8] and shows that no estimator beats tree reconstruction; the second is [YP24, Theorem 38]. The first direction gives $\mathrm{OPT}$ of p.1 at most the tree $\mathrm{OPT}$, which connects Theorem 4.2 to the main theorem.
--
--   Differences from the source:
--   - encoding: OPT_{d,λ} = lim_t E|M_t| → treeOPT = inf_t E|M_t|; reason: E|M_t| is nonincreasing (p.14), so the limit is the infimum
--   - encoding: every estimator σ̂(G) → every sequence of maps from graphs on [n] to laws on labellings; the probability is over (σ⋆, G) and the estimator's coins; reason: an estimator may use internal randomness
--   - reading: an estimator computable in time n^{1+o(1)} → one real-RAM program (no oracle) such that for every θ > 0 there is C_θ with running time ⩽ C_θ N^{1+θ}, N = n + |E(G)| + 2, on every graph, encoding and tape, with output a ±1 labelling; reason: the paper names no machine; worst case is the stronger reading
--   - reading: overlap at least OPT − ε with high probability → the probability over (σ⋆, G) and the tape that the overlap is below OPT − ε, for the worst encoding of G (outer tape measure), tends to 0; reason: the input encoding is chosen adversarially, the stronger reading
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 3.7, p.15 (pdf p.17)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_treeOPT
import Definitions.Def_OptRobustCD_Layouts

namespace OptRobustCD

/-- **Theorem 3.7** (Tree characterization of optimal recovery [MNS16a, YP24]), both clauses.
Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), Theorem 3.7, p.15 (pdf p.17).

"For (G, σ⋆) distributed according to the stochastic block model with parameters d, λ, and every
estimator σ̂(G), and every ε > 0, `Pr(ov(σ̂, σ⋆) > OPT_{d,λ} + ε) −→ 0`. Conversely, for every ε > 0
there is an estimator, computable in time `n^{1+o(1)}`, whose overlap is at least `OPT_{d,λ} − ε`
with high probability."

**Formalization Note.**
* `OPT_{d,λ}` is the tree quantity of §3.3 (`treeOPT`). Standing assumptions of §3.1 (p.12):
  `d > 0`, `λ ∈ (−1, 1)`, `dλ² > 1`.
* First clause: an estimator is any sequence of maps from graphs on `[n]` to laws on labellings
  (it may use internal randomness); the probability is over `(σ⋆, G)` and the estimator's coins.
* Converse: one program of the real RAM (`Machine`, no oracle) such that for every `θ > 0` there is
  `C_θ` with running time at most `C_θ N^{1+θ}`, `N = n + |E(G)| + 2`, on every graph, encoding and
  tape (time `n^{1+o(1)}`), with output a `±1` labelling; and the probability over `(σ⋆, G)` and
  the tape that the overlap is below `OPT_{d,λ} − ε`, for the worst encoding of `G`, tends to `0`
  (outer measure on tapes). -/
theorem theorem_3_7 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) :
    (∀ f : ∀ n : ℕ, SimpleGraph (Fin n) → PMF (Fin n → Bool), ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun n : ℕ => ∑ σ : Fin n → Bool, ∑ G : SimpleGraph (Fin n),
        SBMThreshold.Main.sbmWeight n (sbmA d lam) (sbmB d lam) σ G *
          ((f n G).toOuterMeasure
            {τ | treeOPT d lam + ε < SBMThreshold.Main.overlap σ τ}).toReal)
        Filter.atTop (nhds 0)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ P : Program, NoOracle P ∧
      (∀ θ : ℝ, 0 < θ → ∃ Cθ : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (c : List ℝ), GraphCode G c →
        HaltsWithin P noOracle c (Cθ * ((n : ℝ) + numEdges G + 2) ^ (1 + θ)) ∧
        ∀ ω, IsLabelling n (finalOut P noOracle c ω)) ∧
      Filter.Tendsto (fun n : ℕ => SBMThreshold.Main.sbmExp n (sbmA d lam) (sbmB d lam)
        (fun σ G => ⨆ c : {c : List ℝ // GraphCode G c},
          (tapeMeasure {ω | SBMThreshold.Main.overlap σ
            (labelOfList n (finalOut P noOracle c.1 ω)) < treeOPT d lam - ε}).toReal))
        Filter.atTop (nhds 0)) := by sorry

end OptRobustCD
