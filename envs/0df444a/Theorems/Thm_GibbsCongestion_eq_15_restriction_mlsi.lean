-- Prove2me | Theorems.Thm_GibbsCongestion_eq_15_restriction_mlsi
-- name    : GibbsCongestion.eq_15_restriction_mlsi
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:04:45.413837+00:00
-- url     : https://prove2.me/theorems/80221e20-80e8-4566-82d6-f150e209508b
-- title:
--   Display (15): the restriction chains have $\rho_\alpha\ge\rho_{rt}\ge 1/(n-1)$
-- statement:
--   Throughout, $\Gamma$ is an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing costs $c_e$; $T\ge0$ is the temperature, $\Phi$ is Rosenthal's potential, $\pi$ the Gibbs distribution, and $P$ the relaxed logit dynamics (with probability $\tfrac12$ two random distinct players swap strategies, with probability $\tfrac12$ a logit step).
--
--   For every load profile $\alpha\in\mathcal L$, let $\rho_\alpha$ be the modified log-Sobolev constant of the restriction chain $P_\alpha$ of $P$ to $\mathcal S(\alpha)$, with stationary distribution $\pi_\alpha=\pi/\pi(\mathcal S(\alpha))$ (inside a class only swap moves change the profile). Then
--   $$\rho_\alpha\ \ge\ \rho_{rt}\ \ge\ \frac{1}{n-1},$$
--   where $\rho_{rt}$ is the modified log-Sobolev constant of the random transposition chain on the permutations of $\{1,\dots,n\}$ with its uniform stationary distribution. The chain holds with probability $\tfrac12$ and otherwise composes with a transposition, each transposition having probability $1/(n(n-1))$ (App. B.3, (23)). The second inequality is attributed by the paper to Goel.
--
--   **Formalization Note** For $n=1$ every class is a single profile, $S_1$ is a single permutation and $\rho_\alpha=\rho_{rt}=+\infty$; the paper's $1/(n-1)$ is then undefined and the Lean value $1/0=0$ is used.
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: with probability 1/2 'select two players i, j uniformly at random' and swap them → a uniform ordered pair of distinct players (probability 1/(n(n−1)) each); for n = 1 the swap step is the identity; reason: App. B.3, p.30 computes P_α(s,s′) = 1/(n(n−1)); for n = 1 no pair of distinct players exists
--   - encoding: ρ = inf over f : Ω → ℝ≥0 with Ent_π(f) ≠ 0, real valued → infimum in EReal over f > 0 with Ent_π(f) ≠ 0 (+∞ for an empty index set); reason: functions with zeros do not change the infimum under the paper's conventions (log 0 = −∞), while Lean's log 0 = 0 would; the infimum over ∅ is +∞
--   - reading: L = {α ∈ [q]ⁿ : |α| = n} → L = {α : P → ℕ | Σ_p α_p = n}; reason: the set is used as the set of strategy load profiles (one coordinate per path)
--   - reading: random transposition chain: 'selecting two positions a and b uniformly at random' (p.18), step probabilities given only in App. B.3 → randomTransposition: holding probability 1/2, each transposition probability 1/(n(n−1)); reason: (23), p.30 states P(M, M′) = 1/(n(n−1)) and Σ_{M′∈H(s)} P(M, M′) = P_α(s, s), which forces these values and gives the comparison with C = 1
--   - encoding: 1/(n − 1) at n = 1 (undefined) → 1/0 = 0 in Lean; reason: at n = 1 the paper's bound is undefined; every class and S_1 are single points with ρ_α = ρ_rt = +∞
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, display (15), p.18; proof in App. B.3, pp.29–30

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_gibbs
import Definitions.Def_GibbsCongestion_relaxedLogit
import Definitions.Def_GibbsCongestion_loadClass
import Definitions.Def_GibbsCongestion_mlsiConst
import Definitions.Def_GibbsCongestion_restrictChain
import Definitions.Def_GibbsCongestion_restrictDist
import Definitions.Def_GibbsCongestion_randomTransposition

namespace GibbsCongestion

/-- **Display (15)** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, display (15), p.18; proof App. B.3, pp.29–30). For every load
profile `α ∈ L`, the modified log-Sobolev constant `ρ_α` of the restriction chain of the relaxed
logit dynamics to `S(α)` satisfies `ρ_α ≥ ρ_rt`, and `ρ_rt ≥ 1/(n − 1)`, where `ρ_rt` is the modified
log-Sobolev constant of the random transposition chain with its uniform stationary distribution.

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). `ρ` is `mlsiConst` (values in `EReal`, infimum over positive functions; `+∞` for a chain
whose entropy functional vanishes identically). The step probabilities of the random transposition
chain are those of App. B.3, display (23), p.30 (`randomTransposition`). For `n = 1` every class
`S(α)` is a single profile and `S_1` is a single permutation, so `ρ_α = ρ_rt = +∞`; the paper's
`1/(n − 1)` is undefined there and Lean's `1/0 = 0` is used. -/
theorem eq_15_restriction_mlsi {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) (T : ℝ) (hT : 0 ≤ T) (α : loadProfiles P n) :
    mlsiConst (randomTransposition n) (fun _ => ((n.factorial : ℝ))⁻¹) ≤
        mlsiConst (restrictChain (relaxedLogit P n c T) (loadClass P n) α)
          (restrictDist (gibbs P n c T) (loadClass P n) α) ∧
      (((1 : ℝ) / ((n : ℝ) - 1) : ℝ) : EReal) ≤
        mlsiConst (randomTransposition n) (fun _ => ((n.factorial : ℝ))⁻¹) := by sorry

end GibbsCongestion
