-- Prove2me | Theorems.Thm_FoundationsRL_FuncApprox_bilinucb_pac_bound_v2
-- name    : FoundationsRL.FuncApprox.bilinucb_pac_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:25.493006+00:00
-- url     : https://prove2.me/theorems/51eb027e-b1b1-4050-af90-995150bca447
-- title:
--   Proposition 47 — BiLinUCB PAC guarantee under Bellman rank (v2: normalized rewards, class and embeddings; $K\asymp Hd\log(1+n/d)$)
-- statement:
--   This is **Proposition 47** of Foster & Rakhlin (arXiv:2312.16730v1, p. 140), the PAC guarantee for the BiLinUCB algorithm (§7.3.1) under the Bellman-rank assumption (Definition 8), stated with the standing assumptions of Section 7 made explicit.
--
--   **Setting.** $M^\star$ is a finite-horizon episodic MDP with finite state and action spaces and horizon $H$, with rewards normalized as throughout Section 7: every per-step mean reward lies in $[0,1]$ and $\sum_{h=1}^H r_h\le 1$ along every trajectory of positive probability (`RewardsNormalized`). $\mathcal Q$ is a finite class of value functions $Q=(Q_1,\dots,Q_H)$ with values in $[0,1]$ (`IsNormalizedValueClass`), containing $Q^{M^\star,\star}$ (realizability, encoded by `q0`). $M^\star$ has Bellman rank at most $d$ relative to $\mathcal Q$, witnessed by embeddings $X_h(\pi),W_h(Q)\in\mathbb R^d$ with $E_h(\pi,Q)=\langle X_h(\pi),W_h(Q)\rangle$ for all $\pi\in\Pi^{\rm rns}$, $Q\in\mathcal Q$, $h\in[H]$ (Eq. (7.24)) and $\|X_h(\pi)\|_2,\|W_h(Q)\|_2\le 1$, the normalization the book imposes in its proof (p. 141). BiLinUCB runs $K$ iterations of $n$ episodes: at iteration $k$ it picks $Q_k=\arg\max_{Q\in\mathcal Q_k}\mathbb E_{s_1\sim d_1}[Q_1(s_1,\pi_Q(s_1))]$, plays $\pi_k=\pi_{Q_k}$ for $n$ episodes, forms the empirical residuals $\hat E^k_h(Q)$ and the confidence set $\mathcal Q_{k+1}=\{Q:\sum_{i\le k}(\hat E^i_h(Q))^2\le\beta\ \forall h\}$ (Eq. (7.26)); it outputs $\hat\pi=\pi_{\hat k}$ with $\hat k=\arg\max_k\hat V^k$, $\hat V^k$ the empirical average return of iteration $k$.
--
--   **Theorem.** There are universal constants $c_1,c_2,c_3>0$ such that for every such instance, every $\varepsilon,\delta>0$, every $n\ge 1$ with
--   $$n\ \ge\ c_1\,\frac{H^3 d\log(|\mathcal Q|/\delta)}{\varepsilon^2},\qquad c_2\,Hd\log(1+n/d)\ \le\ K\ \le\ 2c_2\,Hd\log(1+n/d)+1,\qquad \beta=c_3\,\frac{K\log|\mathcal Q|+\log(HK/\delta)}{n},$$
--   BiLinUCB outputs a policy $\hat\pi$ with
--   $$f^{M^\star}(\pi_{M^\star})-f^{M^\star}(\hat\pi)\le\varepsilon$$
--   with probability at least $1-\delta$ over the $Kn$ episodes, where $f^M(\pi)=\mathbb E_{s_1\sim d_1}[V^{M,\pi}_1(s_1)]$.
--
--   **Formalization Note.** The retired version carried no reward bound, so a single lucky episode at reward scale far above $\varepsilon$ (with $n=1$) made the output rule pick the wrong policy (the accepted disproof). The new statement adds the Section 7 standing assumptions as hypotheses: the reward normalization (p. 129, p. 132; the almost-sure cumulative bound is stated along trajectories of positive probability, since the platform's MDP records rewards by their means and identifies realized rewards with those means), the convention that the class is $[0,1]$-valued (p. 132; needed for the Hoeffding step of Lemma 29), and the proof's own normalization $\|X\|_2,\|W\|_2\le 1$ of the Bellman-rank embeddings (p. 141), without which the stated polynomial scalings are not what the book proves (the Bellman-rank definition fixes no scale for the embeddings). "Bellman rank $d$" is encoded as the existence of a normalized rank-$d$ factorization, i.e. rank at most $d$; the guarantee is monotone in $d$, so this contains the exact-rank reading. The book's "$K\gtrsim Hd\log(1+n/d)$" is encoded as a constant-factor window rather than a one-sided bound: with $n$ fixed and $K\to\infty$ the threshold $\beta\propto K$ stops eliminating wrong value functions, and the first-maximizer rule $\arg\max_k\hat V^k$ then selects a lucky bad batch with probability tending to one, so the one-sided reading is false; the window is what the book's proof (Lemma 31 and the final selection step) uses. The universal constants are quantified before every instance; $\delta\le 1$ and $0<K$ are dropped ($K\ge 1$ follows from the window whenever $H,d\ge 1$; for $H=0$ or $d=0$ the claim holds trivially). Ties in every $\arg\max$ are broken by the first maximizer.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 140, Proposition 47 (standing assumptions p. 129, 132; embedding normalization p. 141)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB
import Definitions.Def_FoundationsRL_FuncApprox_Normalization

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

/-- **Proposition 47** (Foster–Rakhlin, arXiv:2312.16730v1, p. 140, Prop. 47), under the
standing assumptions of Section 7 (`RewardsNormalized M`, `[0,1]`-valued class) and the
normalization of the Bellman-rank embeddings the book imposes in its proof (p. 141: "we
assume throughout this proof that `‖X^{M⋆}_h(π)‖₂, ‖W^{M⋆}_h(Q)‖₂ ≤ 1`"): suppose `M⋆` has
Bellman rank at most `d` relative to the finite class realized by `qeval`, witnessed by a
bilinear factorization (7.24) with unit-norm-bounded embeddings, and `Q^{M⋆,⋆} ∈ 𝒬` (`q0`).
For any `ε, δ > 0`, if `n ≥ c₁·H³ d log(|𝒬|/δ)/ε²`, `K ≍ H d log(1 + n/d)` (between `c₂·X` and
`2c₂·X + 1` for `X = H d log(1 + n/d)`) and `β = c₃·(K log|𝒬| + log(HK/δ))/n`, for universal
constants `c₁, c₂, c₃`, then BiLinUCB, run for `K` iterations of `n` episodes each, outputs a
policy `π̂` with `f^{M⋆}(π_{M⋆}) - f^{M⋆}(π̂) ≤ ε` with probability at least `1 - δ`.

Corrected replacement of `bilinucb_pac_bound`: the retired statement omitted the reward
normalization (so rewards could be rescaled far above `ε`), the `[0,1]` range of the class and
the embedding normalization, and it read the book's `K ≳ Hd log(1+n/d)` as a lower bound only;
with `n` fixed and `K → ∞` the threshold `β ∝ K` never eliminates a wrong value function and
the output rule `arg max_k V̂^k` (first maximizer) selects a lucky bad batch with probability
tending to one, so `K` is pinned to a constant-factor window as the book's proof requires.
`δ ≤ 1` and `0 < K` are dropped (the latter is forced by the window whenever `H, d ≥ 1`). -/
theorem bilinucb_pac_bound_v2 :
    ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (_hM : RewardsNormalized M)
        {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (_hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0) (d : ℕ)
        (_hrank : ∃ (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ),
          (∀ π, IsPolicy H π → ∀ Qf : Qc, ∀ h : ℕ, h < H →
              bellmanResidual M π h (qeval Qf) = ∑ j : Fin d, X π h j * W (qeval Qf) h j) ∧
          (∀ π, IsPolicy H π → ∀ h : ℕ, h < H → ∑ j : Fin d, (X π h j) ^ 2 ≤ 1) ∧
          (∀ Qf : Qc, ∀ h : ℕ, h < H → ∑ j : Fin d, (W (qeval Qf) h j) ^ 2 ≤ 1)),
        ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        ∀ n K : ℕ, 0 < n →
          (n : ℝ) ≥ c1 * (H : ℝ) ^ 3 * d * Real.log ((Fintype.card Qc : ℝ) / δ) / ε ^ 2 →
          c2 * ((H : ℝ) * d * Real.log (1 + (n : ℝ) / d)) ≤ K →
          (K : ℝ) ≤ 2 * c2 * ((H : ℝ) * d * Real.log (1 + (n : ℝ) / d)) + 1 →
          ∀ β : ℝ,
            β = c3 * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
            probEvent M (biLinUCBLearner M qeval n β) (K * n)
                (fun histT =>
                  (∑ s : S, M.d1 s * Vstar M 0 s) -
                    (∑ s : S, M.d1 s *
                      V M (biLinUCBOutput M qeval (List.ofFn histT) n β K) 0 s) ≤ ε)
              ≥ 1 - δ := by sorry

end FoundationsRL.FuncApprox
