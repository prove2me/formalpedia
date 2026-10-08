-- Prove2me | Theorems.Thm_FoundationsRL_FuncApprox_confidence_set_validity_v2
-- name    : FoundationsRL.FuncApprox.confidence_set_validity_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:20.10098+00:00
-- url     : https://prove2.me/theorems/b18dc8e9-cf9d-4378-9f4d-1fe099bb5a0c
-- title:
--   Lemma 29 — BiLinUCB confidence-set validity (v2: normalized rewards and class, $|\mathcal Q|\ge 2$)
-- statement:
--   This is **Lemma 29** of Foster & Rakhlin (arXiv:2312.16730v1, p. 142), which validates the confidence sets $\mathcal Q_k$ maintained by BiLinUCB, stated with the standing assumptions of Section 7 made explicit.
--
--   Fix a finite-horizon episodic MDP $M$ with rewards normalized as throughout Section 7 — every per-step mean reward in $[0,1]$ and $\sum_{h=1}^H r_h\le 1$ along every trajectory of positive probability (`RewardsNormalized`) — and a finite class $\mathcal Q$ of $[0,1]$-valued value functions (`IsNormalizedValueClass`) with $|\mathcal Q|\ge 2$ and $Q^{M,\star}\in\mathcal Q$ (encoded by `q0`). BiLinUCB runs $K$ iterations of $n\ge 1$ episodes, playing at iteration $i$ the greedy policy $\pi_i$ of the optimistic $Q_i\in\mathcal Q_i$ and forming $\mathcal Q_{k}=\{Q\in\mathcal Q:\sum_{i<k}(\hat E^i_h(Q))^2\le\beta\ \forall h\in[H]\}$ from the empirical residuals $\hat E^i_h(Q)$ of the first $k-1$ iterations (Eq. (7.26)); $E_h(\pi,Q)=\mathbb E^{M,\pi}[Q_h(s_h,a_h)-r_h-\max_aQ_{h+1}(s_{h+1},a)]$ is the true Bellman residual (Eq. (7.22)).
--
--   **Lemma.** There are absolute constants $c,C>0$ such that for every such instance, every $\delta>0$ and
--   $$\beta=c\cdot\frac{K\log|\mathcal Q|+\log(HK/\delta)}{n},$$
--   with probability at least $1-\delta$ over the $Kn$ episodes, simultaneously for all $k\in[K]$:
--   1. every $Q\in\mathcal Q_k$ satisfies $\sum_{i<k}E_h(\pi_i,Q)^2\le C\beta$ for all $h\in[H]$ (Eq. (7.27));
--   2. $Q^{M,\star}\in\mathcal Q_k$.
--
--   **Formalization Note.** The retired version carried no bound on the rewards or on the class, so rescaling the rewards pushed the empirical residual of $Q^\star$ above $\beta$ on every trajectory (the accepted disproof). The new statement adds the Section 7 reward normalization (p. 129, p. 132; the almost-sure cumulative bound is stated along trajectories of positive probability, since the platform's MDP records rewards by their means and identifies realized rewards with those means) and the convention that the class is $[0,1]$-valued (p. 132), which together bound the residual summands so that Hoeffding's inequality applies with absolute constants. It also corrects the printed statement at $|\mathcal Q|=1$: there $\beta=c\log(HK/\delta)/n$, while $\sum_{i<k}(\hat E^i_h(Q^\star))^2\approx k\,\mathrm{Var}/n$ grows linearly in $k$ (e.g. with $n=1$ it is exactly $k/4$ in a two-state MDP with a fair transition), so $Q^\star$ leaves $\mathcal Q_k$ for large $K$ with certainty — the printed proof drops the factor $k$ when it sums (7.28) over $i<k$; for $|\mathcal Q|\ge 2$ the term $K\log|\mathcal Q|\ge K\log 2$ in $\beta$ absorbs the sum. The absolute constants $c$ (in $\beta$) and $C$ (in (7.27)) are quantified before every instance; the retired hypothesis $\delta\le 1$ is dropped; the iterations are $0$-indexed ($\mathcal Q_k$ uses iterations $i<k$, $\mathcal Q_0=\mathcal Q$); $\arg\max$ ties are broken by the first maximizer.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 142, Lemma 29 (Eqs. (7.27), (7.28)); standing assumptions p. 129, 132 — corrected transcription: the hypothesis |𝒬| ≥ 2 is added, the printed statement being false for |𝒬| = 1

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB
import Definitions.Def_FoundationsRL_FuncApprox_Normalization

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

/-- **Lemma 29** (Foster–Rakhlin, arXiv:2312.16730v1, p. 142, Lemma 29), under the standing
assumptions of Section 7: rewards normalized (`RewardsNormalized M`: per-step rewards in
`[0,1]` and `Σ_h r_h ≤ 1` along every trajectory of positive probability), a `[0,1]`-valued
value-function class (`IsNormalizedValueClass`) with `Q^{M⋆,⋆} ∈ 𝒬` (encoded by `q0`) and at
least two members. For any `δ > 0`, if `β = c · (K·log|𝒬| + log(HK/δ)) / n` for a sufficiently
large absolute constant `c`, then with probability at least `1 - δ` over BiLinUCB's `K·n`
episodes, simultaneously for all iterations `k ∈ [K]`: (1) every `Q` retained in the
confidence set `𝒬_k` has, at every layer, its true Bellman residual along the played policies
`π_1,…,π_{k-1}` summing in square to at most an absolute constant `C` times `β` (Eq. (7.27));
(2) `Q^{M⋆,⋆} ∈ 𝒬_k`.

Corrected replacement of `confidence_set_validity`: the retired statement omitted the
Section 7 reward normalization and the `[0,1]` range of the class, so rescaling the rewards
pushed the empirical residual of `Q^⋆` above `β`. The hypothesis `1 < |𝒬|` corrects the printed
statement, which is false for `|𝒬| = 1`: then `β = c·log(HK/δ)/n` while
`Σ_{i<k} (Ê^i_h(Q^⋆))² ≈ k·Var/n` grows linearly in `k` (the printed proof drops the factor `k`
when summing (7.28) over `i < k`); for `|𝒬| ≥ 2` the term `K·log|𝒬| ≥ K·log 2` restores the
claim. The superfluous `δ ≤ 1` is dropped. -/
theorem confidence_set_validity_v2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (_hM : RewardsNormalized M)
        {Qc : Type} [Fintype Qc] [Nonempty Qc] (_hQc : 1 < Fintype.card Qc)
        (qeval : Qc → ℕ → S → A → ℝ) (_hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (n K : ℕ) (δ : ℝ), 0 < n → 0 < δ →
        ∀ β : ℝ, β = c * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
        probEvent M (biLinUCBLearner M qeval n β) (K * n)
            (fun histT =>
              ∀ k, k < K →
                (∀ Qf ∈ confSet M qeval (List.ofFn histT) n β k, ∀ h : Fin H,
                    ∑ i ∈ Finset.range k,
                      (bellmanResidual M (iterPolicy M qeval (List.ofFn histT) n β i) h.1
                        (qeval Qf)) ^ 2 ≤ C * β) ∧
                q0 ∈ confSet M qeval (List.ofFn histT) n β k)
          ≥ 1 - δ := by sorry

end FoundationsRL.FuncApprox
