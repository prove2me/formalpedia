-- Prove2me | Theorems.Thm_GibbsCongestion_eq_14_projection_mlsi
-- name    : GibbsCongestion.eq_14_projection_mlsi
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:05:09.341409+00:00
-- url     : https://prove2.me/theorems/99abf862-a61b-4ec4-a153-4fc56754282d
-- title:
--   Display (14): $\bar\rho\ge 1/(n\max(n,2))$ (corrected: $1/n^2\to1/(n\max(n,2))$)
-- statement:
--   Throughout, $\Gamma$ is an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing costs $c_e$; $T\ge0$ is the temperature, $\Phi$ is Rosenthal's potential, $\pi$ the Gibbs distribution, and $P$ the relaxed logit dynamics (with probability $\tfrac12$ two random distinct players swap strategies, with probability $\tfrac12$ a logit step).
--
--   Let $\bar\rho$ be the modified log-Sobolev constant of the projection chain $\bar P$ of $P$ on the load-profile partition $\{\mathcal S(\alpha)\}_{\alpha\in\mathcal L}$, with stationary distribution $\bar\pi(\alpha)=\pi(\mathcal S(\alpha))$. Then
--   $$\rho(\Pi(\mathcal L))\ \ge\ \frac1n\qquad\text{and}\qquad\bar\rho\ \ge\ \frac{1}{n\,\max(n,2)},$$
--   where $\rho(\Pi(\mathcal L))$ is the modified log-Sobolev constant of the base-exchange chain on the support of the polarization $\Pi(g)$ of $g$ in (11) (Cryan, Guo and Mousa). For $n\ge2$ the second bound is the paper's $\bar\rho\ge1/n^2$; it combines the first inequality of (14), stated in `eq_14_projection_comparison`, with the first bound here.
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: with probability 1/2 'select two players i, j uniformly at random' and swap them → a uniform ordered pair of distinct players (probability 1/(n(n−1)) each); for n = 1 the swap step is the identity; reason: App. B.3, p.30 computes P_α(s,s′) = 1/(n(n−1)); for n = 1 no pair of distinct players exists
--   - encoding: ρ = inf over f : Ω → ℝ≥0 with Ent_π(f) ≠ 0, real valued → infimum in EReal over f > 0 with Ent_π(f) ≠ 0 (+∞ for an empty index set); reason: functions with zeros do not change the infimum under the paper's conventions (log 0 = −∞), while Lean's log 0 = 0 would; the infimum over ∅ is +∞
--   - reading: L = {α ∈ [q]ⁿ : |α| = n} → L = {α : P → ℕ | Σ_p α_p = n}; reason: the set is used as the set of strategy load profiles (one coordinate per path)
--   - correction: ρ̄ ≥ 1/n² → ρ̄ ≥ 1/(n·max(n, 2)); reason: false at n = 1: two parallel arcs with π = (0.99, 0.01) and f = (1, 100) give a Dirichlet-to-entropy ratio ≈ 0.6975 < 1; for n ≥ 2 the statement is the printed one
--   - encoding: base-exchange Markov chain on the support of Π(g), g as in (11) → baseExchangeWalk on the n-subsets of P × Fin n with weights polarWeight; reason: by (10) polarWeight B is the coefficient of y^B in Π(g); it is positive on every n-subset, so the support is the set of bases of the n-uniform matroid (p.16, App. B.3, p.28)
--   - reading: ground set {(i, j) : 1 ≤ i, j ≤ n} (p.16) and F_i for i = 1, …, n (App. B.3, p.28) → ground set P × Fin n; reason: App. B.3: for every path p we introduce n auxiliary elements, one group per path, as in Lemma 4.3's one variable per path
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, display (14), p.17

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_gibbs
import Definitions.Def_GibbsCongestion_relaxedLogit
import Definitions.Def_GibbsCongestion_loadClass
import Definitions.Def_GibbsCongestion_mlsiConst
import Definitions.Def_GibbsCongestion_projChain
import Definitions.Def_GibbsCongestion_baseExchangeWalk
import Definitions.Def_GibbsCongestion_baseExchangeDist
import Definitions.Def_GibbsCongestion_polarWeight

namespace GibbsCongestion

/-- **Display (14), corrected** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, display (14), p.17). The modified log-Sobolev constant of
the projection chain of the relaxed logit dynamics on load profiles satisfies
`ρ̄ ≥ 1/(n · max(n, 2))`, and the modified log-Sobolev constant of the base-exchange chain on the
support of `Π(g)` satisfies `ρ(Π(L)) ≥ 1/n` (the second inequality of (14), by Cryan, Guo and Mousa).

**Correction** The paper prints `ρ̄ ≥ 1/n²`, false at `n = 1` (two parallel arcs, `π = (0.99, 0.01)`,
`f = (1, 100)`: the Dirichlet-to-entropy ratio is `≈ 0.6975 < 1`). For `n ≥ 2` the statement is the
printed one.

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). `ρ` is `mlsiConst` (values in `EReal`, infimum over positive functions; `+∞` for a chain
whose entropy functional vanishes identically). -/
theorem eq_14_projection_mlsi {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) (T : ℝ) (hT : 0 ≤ T) :
    (((1 : ℝ) / (n : ℝ) : ℝ) : EReal) ≤
        mlsiConst
          (baseExchangeWalk ((Finset.univ : Finset (P × Fin n)).powersetCard n) (polarWeight P n c T))
          (baseExchangeDist ((Finset.univ : Finset (P × Fin n)).powersetCard n) (polarWeight P n c T)) ∧
      (((1 : ℝ) / ((n : ℝ) * ((max n 2 : ℕ) : ℝ)) : ℝ) : EReal) ≤
        mlsiConst (projChain (relaxedLogit P n c T) (gibbs P n c T) (loadClass P n))
          (projDist (gibbs P n c T) (loadClass P n)) := by sorry

end GibbsCongestion
