-- Prove2me | Theorems.Thm_GibbsCongestion_relaxed_logit_mlsi
-- name    : GibbsCongestion.relaxed_logit_mlsi
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:04:24.922762+00:00
-- url     : https://prove2.me/theorems/119edd12-f7c1-49d3-90ad-ffb43e076c5e
-- title:
--   Modified log-Sobolev constant of the relaxed logit dynamics: $\rho\ge1/(n^2\max(n,2))$ (corrected: $1/n^3\to1/(n^2\max(n,2))$; $\bar\rho$ read as $\rho$)
-- statement:
--   Throughout, $\Gamma$ is an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing costs $c_e$; $T\ge0$ is the temperature, $\Phi$ is Rosenthal's potential, $\pi$ the Gibbs distribution, and $P$ the relaxed logit dynamics (with probability $\tfrac12$ two random distinct players swap strategies, with probability $\tfrac12$ a logit step).
--
--   The modified log-Sobolev constant of the relaxed logit dynamics with its Gibbs distribution satisfies
--   $$\rho(P)\ \ge\ \frac{1}{n^2\max(n,2)}.$$
--   For $n\ge2$ this is $\rho\ge1/n^3$, the bound the paper derives from (13), (14) and (15) and plugs into the mixing-time bound (7).
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: with probability 1/2 'select two players i, j uniformly at random' and swap them → a uniform ordered pair of distinct players (probability 1/(n(n−1)) each); for n = 1 the swap step is the identity; reason: App. B.3, p.30 computes P_α(s,s′) = 1/(n(n−1)); for n = 1 no pair of distinct players exists
--   - encoding: ρ = inf over f : Ω → ℝ≥0 with Ent_π(f) ≠ 0, real valued → infimum in EReal over f > 0 with Ent_π(f) ≠ 0 (+∞ for an empty index set); reason: functions with zeros do not change the infimum under the paper's conventions (log 0 = −∞), while Lean's log 0 = 0 would; the infimum over ∅ is +∞
--   - reading: 'applying Theorem A.2, it follows that ρ̄ ≥ 1/n³' → a bound on ρ, the constant of the whole relaxed chain; reason: the next sentence plugs the bound into (7), which needs ρ of the whole chain; the decomposition is Theorem A.1
--   - correction: ρ ≥ 1/n³ → ρ ≥ 1/(n²·max(n, 2)); reason: false at n = 1: two parallel arcs with π = (0.99, 0.01) and f = (1, 100) give ratio ≈ 0.6975 < 1; for n ≥ 2 the statement is the printed one
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.18

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_gibbs
import Definitions.Def_GibbsCongestion_relaxedLogit
import Definitions.Def_GibbsCongestion_mlsiConst

namespace GibbsCongestion

/-- **Modified log-Sobolev constant of the relaxed logit dynamics, corrected**
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.18). The modified log-Sobolev constant of the relaxed logit dynamics with its Gibbs
distribution satisfies `ρ ≥ 1/(n² · max(n, 2))`.

**Correction** The paper prints "`ρ̄ ≥ 1/n³`", obtained from (14) and (15) by the decomposition
theorem and used in (7) as the constant `ρ` of the whole chain; it is read as a bound on `ρ`. At
`n = 1` the printed `1/n³ = 1` is false (two parallel arcs, `π = (0.99, 0.01)`, `f = (1, 100)` give
ratio `≈ 0.6975`). For `n ≥ 2` the statement is `ρ ≥ 1/n³`.

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). `ρ` is `mlsiConst` (values in `EReal`, infimum over positive functions; `+∞` for a chain
whose entropy functional vanishes identically). -/
theorem relaxed_logit_mlsi {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) (T : ℝ) (hT : 0 ≤ T) :
    (((1 : ℝ) / ((n : ℝ) ^ 2 * ((max n 2 : ℕ) : ℝ)) : ℝ) : EReal) ≤
      mlsiConst (relaxedLogit P n c T) (gibbs P n c T) := by sorry

end GibbsCongestion
