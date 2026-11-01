-- Prove2me | Theorems.Thm_GibbsCongestion_cryan_guo_mousa_mlsi
-- name    : GibbsCongestion.cryan_guo_mousa_mlsi
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:02:21.656728+00:00
-- url     : https://prove2.me/theorems/98c1045c-25d1-4959-9ef6-783e71782e0a
-- title:
--   Cryan–Guo–Mousa: the base-exchange walk under an SLC distribution has $\rho\ge 1/r$
-- statement:
--   Let $\mathcal N$ be a matroid of rank $r$ on a finite ground set, and $w\ge0$ a weight function on its bases such that the generating polynomial
--   $$\sum_{B\text{ base}}w(B)\prod_{e\in B}x_e$$
--   is strongly log-concave (the distribution $\pi(B)\propto w(B)$ is SLC). Then the modified log-Sobolev constant of the base-exchange random walk with stationary distribution $\pi$ satisfies
--   $$\rho\ \ge\ \frac1r.$$
--
--   This is the external input to the second inequality of (14), applied to the $n$-uniform matroid of rank $n$.
--
--   **Formalization Note** The walk lives on the bases of positive weight. The constant is valued in the extended reals ($+\infty$ when the entropy functional vanishes identically). The rank is `M.eRank`; for $r=0$ the right side is $1/0=0$.
--
--   Differences from the source:
--   - encoding: ρ = inf over f : Ω → ℝ≥0 with Ent_π(f) ≠ 0, real valued → infimum in EReal over f > 0 with Ent_π(f) ≠ 0 (+∞ for an empty index set); reason: functions with zeros do not change the infimum under the paper's conventions (log 0 = −∞), while Lean's log 0 = 0 would; the infimum over ∅ is +∞
--   - reading: log-concave on a subset S ⊆ ℝⁿ≥0 (S unspecified) → log-concave on the open positive orthant; reason: the convention of the cited works (Anari et al.; Brändén–Huh)
--   - encoding: base-exchange chain on the set of all bases → the chain on the bases of positive weight, with π(B) = w(B)/Σ w; reason: a base of weight 0 has π = 0 and the chain never enters it; the Lean state space is the support of π, where the chain is the page's
--   - encoding: 1/r for a matroid of rank r → 1/0 = 0 at r = 0; reason: at r = 0 the only base is ∅, the walk has at most one state and ρ = +∞ as the empty infimum, so nothing is claimed there
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11 (result of Cryan, Guo and Mousa [15])

import Mathlib
import Definitions.Def_GibbsCongestion_IsSLC
import Definitions.Def_GibbsCongestion_mlsiConst
import Definitions.Def_GibbsCongestion_baseExchangeWalk
import Definitions.Def_GibbsCongestion_baseExchangeDist

namespace GibbsCongestion

open Classical in
/-- **Cryan, Guo and Mousa** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11, unnumbered). Let `M` be a matroid of rank
`r` on a finite ground set and `w ≥ 0` a weight function on its bases whose generating polynomial
`∑_B w(B) ∏_{e ∈ B} x_e` is strongly log-concave (the distribution `π(B) ∝ w(B)` is SLC). Then the
modified log-Sobolev constant of the base-exchange random walk satisfies `ρ ≥ 1/r`.

**Formalization Note** The walk lives on the bases of positive weight, with stationary distribution
`π(B) = w(B)/∑ w`. `ρ` is `mlsiConst` (values in `EReal`, infimum over positive functions; `+∞` for a chain
whose entropy functional vanishes identically). The rank is `M.eRank`. For `r = 0` the right side is `1/0 = 0`. -/
theorem cryan_guo_mousa_mlsi {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (r : ℕ)
    (hr : M.eRank = r) (w : Finset α → ℝ) (hw : ∀ B : Finset α, M.IsBase (B : Set α) → 0 ≤ w B)
    (hslc : IsSLC (∑ B ∈ Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α)),
      MvPolynomial.C (w B) * ∏ e ∈ B, MvPolynomial.X e)) :
    (((1 : ℝ) / r : ℝ) : EReal) ≤
      mlsiConst (baseExchangeWalk (Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α))) w)
        (baseExchangeDist (Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α))) w) := by sorry

end GibbsCongestion
