-- Prove2me | Theorems.Thm_GibbsCongestion_eq_14_projection_comparison
-- name    : GibbsCongestion.eq_14_projection_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:04:31.913689+00:00
-- url     : https://prove2.me/theorems/b3ef5be6-f12d-4038-95e5-6f66084a2f3e
-- title:
--   Display (14), first inequality: $\bar\rho\ge\rho(\Pi(\mathcal L))/\max(n,2)$ (corrected: $1/n\to1/\max(n,2)$)
-- statement:
--   Throughout, $\Gamma$ is an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing costs $c_e$; $T\ge0$ is the temperature, $\Phi$ is Rosenthal's potential, $\pi$ the Gibbs distribution, and $P$ the relaxed logit dynamics (with probability $\tfrac12$ two random distinct players swap strategies, with probability $\tfrac12$ a logit step).
--
--   Let $\bar\rho$ be the modified log-Sobolev constant of the projection chain $\bar P$ of $P$ on the load-profile partition $\{\mathcal S(\alpha)\}_{\alpha\in\mathcal L}$, with stationary distribution $\bar\pi(\alpha)=\pi(\mathcal S(\alpha))$. Let $\rho(\Pi(\mathcal L))$ be the modified log-Sobolev constant of the base-exchange Markov chain on the support of the polarization $\Pi(g)$ of $g$ in (11): the $n$-element subsets $B$ of $\mathcal P\times[n]$ (the bases of the $n$-uniform matroid), with weights $w_\Pi(B)=\binom{n}{\alpha(B)}^{-1}\frac{n!}{\alpha(B)!}e^{-T\Phi(\alpha(B))}$ of (10). Then
--   $$\bar\rho\ \ge\ \frac{1}{\max(n,2)}\,\rho(\Pi(\mathcal L)).$$
--   For $n\ge2$ this is the paper's $\bar\rho\ge\frac1n\rho(\Pi(\mathcal L))$.
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: with probability 1/2 'select two players i, j uniformly at random' and swap them → a uniform ordered pair of distinct players (probability 1/(n(n−1)) each); for n = 1 the swap step is the identity; reason: App. B.3, p.30 computes P_α(s,s′) = 1/(n(n−1)); for n = 1 no pair of distinct players exists
--   - encoding: ρ = inf over f : Ω → ℝ≥0 with Ent_π(f) ≠ 0, real valued → infimum in EReal over f > 0 with Ent_π(f) ≠ 0 (+∞ for an empty index set); reason: functions with zeros do not change the infimum under the paper's conventions (log 0 = −∞), while Lean's log 0 = 0 would; the infimum over ∅ is +∞
--   - reading: L = {α ∈ [q]ⁿ : |α| = n} → L = {α : P → ℕ | Σ_p α_p = n}; reason: the set is used as the set of strategy load profiles (one coordinate per path)
--   - correction: n = 1 included in ρ̄ ≥ (1/n)·ρ(Π(L)) → ρ̄ ≥ ρ(Π(L))/max(n, 2); reason: false at n = 1: the projection chain is then (I + K)/2 with K the base-exchange (logit) step; two parallel arcs with π = (0.99, 0.01) give ρ̄ ≈ 0.6975 < ρ(K) ≈ 1.39. For n ≥ 2, max(n, 2) = n and the statement is the printed one
--   - encoding: base-exchange Markov chain on the support of Π(g), g as in (11) → baseExchangeWalk on the n-subsets of P × Fin n with weights polarWeight; reason: by (10) polarWeight B is the coefficient of y^B in Π(g); it is positive on every n-subset, so the support is the set of bases of the n-uniform matroid (p.16, App. B.3, p.28)
--   - reading: ground set {(i, j) : 1 ≤ i, j ≤ n} (p.16) and F_i for i = 1, …, n (App. B.3, p.28) → ground set P × Fin n; reason: App. B.3: for every path p we introduce n auxiliary elements, one group per path, as in Lemma 4.3's one variable per path
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, display (14), first inequality, p.17; proof in App. B.3, pp.28–29

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

/-- **Display (14), first inequality, corrected** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, display (14), p.17; proof App. B.3,
pp.28–29). The modified log-Sobolev constant `ρ̄` of the projection chain of the relaxed logit
dynamics on load profiles satisfies `ρ̄ ≥ ρ(Π(L)) / max(n, 2)`, where `ρ(Π(L))` is the modified
log-Sobolev constant of the base-exchange chain on the support of the polarization `Π(g)` of `g` in
(11) (the bases of the `n`-uniform matroid on `P × [n]`, weights `w_Π` of (10)).

**Correction** The paper prints `ρ̄ ≥ (1/n) ρ(Π(L))`. At `n = 1` it is false: the projection chain is
then the whole chain `(I + K)/2` with `K` the base-exchange (logit) step, and for two parallel arcs
with `π = (0.99, 0.01)` one gets `ρ̄ ≈ 0.6975 < ρ(K) ≈ 1.39`. For every `n ≥ 2`, `max(n, 2) = n` and
the statement is the printed one.

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). `ρ` is `mlsiConst` (values in `EReal`, infimum over positive functions; `+∞` for a chain
whose entropy functional vanishes identically). The partition is `s ↦ z(s)` (`loadClass`). -/
theorem eq_14_projection_comparison {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) (T : ℝ) (hT : 0 ≤ T) :
    mlsiConst
        (baseExchangeWalk ((Finset.univ : Finset (P × Fin n)).powersetCard n) (polarWeight P n c T))
        (baseExchangeDist ((Finset.univ : Finset (P × Fin n)).powersetCard n) (polarWeight P n c T)) / ((max n 2 : ℕ) : EReal) ≤
      mlsiConst (projChain (relaxedLogit P n c T) (gibbs P n c T) (loadClass P n))
        (projDist (gibbs P n c T) (loadClass P n)) := by sorry

end GibbsCongestion
