-- Prove2me | Theorems.Thm_GibbsCongestion_projection_adjacent_transition
-- name    : GibbsCongestion.projection_adjacent_transition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:04:15.793528+00:00
-- url     : https://prove2.me/theorems/09c8a401-7ff2-41b7-bc80-a6e649992346
-- title:
--   Displays (12)–(13): projection-chain transitions between adjacent load profiles
-- statement:
--   Throughout, $\Gamma$ is an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing costs $c_e$; $T\ge0$ is the temperature, $\Phi$ is Rosenthal's potential, $\pi$ the Gibbs distribution, and $P$ the relaxed logit dynamics (with probability $\tfrac12$ two random distinct players swap strategies, with probability $\tfrac12$ a logit step).
--
--   Partition $\mathcal P^n$ by strategy load profiles, $\Omega_\alpha=\mathcal S(\alpha)$ for $\alpha\in\mathcal L$, and let $\bar P$ be the projection chain of $P$ with respect to $\pi$. Let $s$ be a profile, $i$ a player with $s_i=p$, $p'\ne p$ a path, and $s'=(p',s_{-i})$; so $\alpha=z(s)$ and $\beta=z(s')$ are adjacent load profiles differing on $p$ and $p'$. Then
--   $$\bar P(\alpha,\beta)=\alpha_p\,P(s,s')\qquad(12)$$
--   and consequently
--   $$\frac{P(s,s')}{\bar P(\alpha,\beta)}=\frac1{\alpha_p}\ \ge\ \frac1n.\qquad(13)$$
--
--   The bound $1/n$ is the lower bound on the quantity $\chi$ of the Hermon–Salez decomposition used to pass from the projection and restriction chains to the whole chain.
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: with probability 1/2 'select two players i, j uniformly at random' and swap them → a uniform ordered pair of distinct players (probability 1/(n(n−1)) each); for n = 1 the swap step is the identity; reason: App. B.3, p.30 computes P_α(s,s′) = 1/(n(n−1)); for n = 1 no pair of distinct players exists
--   - reading: (13) 'for any α, β ∈ L, s ∈ S(α) and s′ ∈ S(β)' → s′ = (p′, s₋ᵢ) obtained from s by one deviation of a player i from s_i = p to p′ ≠ p; reason: (13) is derived from (12), which is stated for such pairs; for other pairs P(s, s′) = 0 and the identity is not meant
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, proof of Theorem 4.4, displays (12) and (13), p.17

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_gibbs
import Definitions.Def_GibbsCongestion_relaxedLogit
import Definitions.Def_GibbsCongestion_loadClass
import Definitions.Def_GibbsCongestion_projChain

namespace GibbsCongestion

/-- **Displays (12)–(13)** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, p.17). Let `s` be a profile, `i` a player with `s_i = p`,
and `s' = (p', s₋ᵢ)` with `p' ≠ p`, so that `α = z(s)` and `β = z(s')` are adjacent load profiles
differing on `p` and `p'`. For the relaxed logit chain `P` with Gibbs distribution `π` and the
projection chain `P̄` on load profiles,
`P̄(α, β) = α_p · P(s, s')`  (12),  and hence  `P(s, s') / P̄(α, β) = 1/α_p ≥ 1/n`  (13).

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). The paper's "for any `α, β ∈ L`, `s ∈ S(α)`, `s' ∈ S(β)`" in (13) is read for the pairs
it is derived for: adjacent `α, β` and `s, s'` differing by one deviation (otherwise
`P(s, s') = 0`). -/
theorem projection_adjacent_transition {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e))
    (T : ℝ) (hT : 0 ≤ T) (s : Fin n → P) (i : Fin n) (p' : P) (hp' : s i ≠ p') :
    projChain (relaxedLogit P n c T) (gibbs P n c T) (loadClass P n)
        (loadClass P n s) (loadClass P n (Function.update s i p')) =
      (strategyLoad s (s i) : ℝ) * relaxedLogit P n c T s (Function.update s i p') ∧
    relaxedLogit P n c T s (Function.update s i p') /
        projChain (relaxedLogit P n c T) (gibbs P n c T) (loadClass P n)
          (loadClass P n s) (loadClass P n (Function.update s i p')) =
      1 / (strategyLoad s (s i) : ℝ) ∧
    (1 : ℝ) / n ≤ 1 / (strategyLoad s (s i) : ℝ) := by sorry

end GibbsCongestion
