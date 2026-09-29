-- Prove2me | Theorems.Thm_FoundationsRL_FuncApprox_bilinucb_pac_bound
-- name    : FoundationsRL.FuncApprox.bilinucb_pac_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:29:41.194315+00:00
-- url     : https://prove2.me/theorems/f3d1ef81-cc71-46e7-aac9-062b76e59c04
-- title:
--   Proposition 47 — BiLinUCB PAC guarantee under Bellman rank
-- statement:
--   This is **Proposition 47** of Foster & Rakhlin, *Foundations of Reinforcement Learning
--   and Interactive Decision Making* (arXiv:2312.16730v1, p. 140), the chapter's main
--   sample-complexity (PAC) guarantee for reinforcement learning under the Bellman rank
--   structural assumption (Definition 8, `FuncApprox.IsBellmanRank`).
--
--   Suppose the true MDP $M^\star$ has Bellman rank $d$ relative to a finite value-function
--   class $\mathcal Q$ (realized via `qeval`), and $Q^{M^\star,\star}\in\mathcal Q$
--   (realizability, encoded by `q0`). For any $\varepsilon,\delta>0$, if the batch size $n$,
--   iteration count $K$, and confidence-set threshold $\beta$ satisfy
--   $$
--   n \gtrsim \frac{H^3 d \log(|\mathcal Q|/\delta)}{\varepsilon^2}, \qquad
--   K \gtrsim H d \log(1+n/d), \qquad
--   \beta \propto \frac{K\log|\mathcal Q|+\log(HK/\delta)}{n}
--   $$
--   for universal constants, then the **BiLinUCB** algorithm (`FuncApprox.BiLinUCB`), run for
--   $K$ iterations of $n$ episodes each, outputs a policy $\hat\pi$ with
--   $$
--   f^{M^\star}(\pi^{M^\star}) - f^{M^\star}(\hat\pi) \le \varepsilon
--   $$
--   with probability at least $1-\delta$, where
--   $f^M(\pi) = \mathbb E_{s_1\sim d_1}[V_1^{M,\pi}(s_1)]$ is the expected return of $\pi$
--   under $M$.
--
--   Unlike the regret bounds proved elsewhere in this chapter and book, this is a **PAC
--   (probably-approximately-correct) guarantee**: BiLinUCB collects $Kn$ episodes of training
--   data and only then commits to a single final policy $\hat\pi$, whose *post-training*
--   suboptimality is bounded — it is not a bound on cumulative regret accrued during the $Kn$
--   training episodes themselves. The sample complexity depends only on the horizon $H$, the
--   Bellman rank $d$, and the value-function class's capacity $\log|\mathcal Q|$, not on the
--   size of the state space.
--
--   **Formalization Note** The universal constants $c_1,c_2,c_3$ scaling $n$, $K$, and
--   $\beta$ are existentially quantified ahead of every MDP, value-function class and
--   $(\varepsilon,\delta)$, matching the book's `≳`/`∝` notation. $f^{M^\star}(\pi^{M^\star})$
--   is represented as $\sum_s d_1(s)\,V^\star_1(s)$ (the optimal value), avoiding the need to
--   name a maximizing policy explicitly.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 140, Proposition 47

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

/-- **Proposition 47** (Foster–Rakhlin, arXiv:2312.16730v1, p. 140, Prop. 47): suppose `M⋆`
has Bellman rank `d` relative to the (finite) value-function class realized by `qeval`, and
`Q^{M⋆,⋆} ∈ Q` (encoded by `q0`). For any `ε, δ > 0`, if the batch size `n`, iteration count
`K`, and confidence-set threshold `β` satisfy the book's stated scalings (for universal
constants `c1, c2, c3 > 0`), then BiLinUCB, run for `K` iterations of `n` episodes each,
outputs a policy `π̂` with `f^{M⋆}(π^{M⋆}) - f^{M⋆}(π̂) ≤ ε` with probability at least `1 - δ`.
This is a PAC (sample-complexity) guarantee for BiLinUCB's *final* output policy, not a regret
bound over the `K·n` training episodes. -/
theorem bilinucb_pac_bound :
    ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
        (hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0) (d : ℕ),
        IsBellmanRank M {Q | ∃ Qf : Qc, qeval Qf = Q} d →
        ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 →
        ∀ n K : ℕ, 0 < n → 0 < K →
          (n : ℝ) ≥ c1 * (H : ℝ) ^ 3 * d * Real.log (Fintype.card Qc / δ) / ε ^ 2 →
          (K : ℝ) ≥ c2 * H * d * Real.log (1 + (n : ℝ) / d) →
          ∀ β : ℝ,
            β = c3 * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
            probEvent M (biLinUCBLearner M qeval n β) (K * n)
                (fun histT =>
                  (∑ s : S, M.d1 s * Vstar M 0 s) -
                    (∑ s : S, M.d1 s *
                      V M (biLinUCBOutput M qeval (List.ofFn histT) n β K) 0 s) ≤ ε)
              ≥ 1 - δ := by sorry

end FoundationsRL.FuncApprox
