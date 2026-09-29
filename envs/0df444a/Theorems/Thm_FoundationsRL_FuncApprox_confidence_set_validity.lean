-- Prove2me | Theorems.Thm_FoundationsRL_FuncApprox_confidence_set_validity
-- name    : FoundationsRL.FuncApprox.confidence_set_validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:28:03.905793+00:00
-- url     : https://prove2.me/theorems/08068b60-b8b2-4249-9e26-e0b911b9fdc5
-- title:
--   Lemma 29 — BiLinUCB confidence-set validity
-- statement:
--   This is Lemma 29 of Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making* (arXiv:2312.16730v1, p. 142), which validates the
--   confidence sets $\mathcal Q_k$ maintained by the BiLinUCB algorithm
--   (`FuncApprox.BiLinUCB`).
--
--   Fix a finite-horizon episodic MDP $M$, a finite value-function class $\mathcal Q$
--   (realized via `qeval`), and suppose $Q^{M,\star} \in \mathcal Q$ (encoded by `q0`,
--   matching the optimal value function `Qstar` of the underlying MDP). For any $\delta>0$,
--   set the confidence-set threshold
--   $$
--   \beta = c \cdot \frac{K\log|\mathcal Q| + \log(HK/\delta)}{n}
--   $$
--   for a sufficiently large absolute constant $c$. Then, running BiLinUCB for $K$
--   iterations of $n$ episodes each, with probability at least $1-\delta$ over the $Kn$
--   realized episodes, simultaneously for every iteration $k \in [K]$:
--
--   1. every value function $Q$ retained in the confidence set $\mathcal Q_k$ has, at every
--      layer $h$, its *true* Bellman residual along the policies $\pi_1,\dots,\pi_{k-1}$
--      actually played summing in square to at most a constant times $\beta$;
--   2. the realizable value function $Q^{M,\star}$ is itself retained in $\mathcal Q_k$.
--
--   This is the deterministic-looking guarantee (valid on a probability-$(1-\delta)$ event)
--   that the confidence sets never discard the truth, and never retain a badly-fitting
--   function, that Lemma 30 and Proposition 47 build on.
--
--   **Formalization Note** The universal constants $c$ (in $\beta$) and $C$ (in the residual
--   bound) are existentially quantified ahead of every instance $(S,A,H,M,\mathcal
--   Q,\dots)$, matching the book's `≲` notation: they do not depend on the particular MDP or
--   value-function class.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 142, Lemma 29 (Eq. 7.27, 7.28)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

/-- **Lemma 29** (Foster–Rakhlin, arXiv:2312.16730v1, p. 142, Lemma 29): for any `δ > 0`, if
`β = c · (K·log|Q| + log(HK/δ)) / n` for a sufficiently large absolute constant `c`, then with
probability at least `1 - δ` over BiLinUCB's `K·n` episodes, simultaneously for all iterations
`k ∈ [K]`: (1) every `Q` retained in the confidence set `Q_k` has, at every layer, its true
Bellman residual along the played policies `π_1,…,π_{k-1}` summing (in square) to at most a
constant times `β`; (2) the realizable value function `Q^{M⋆,⋆}` (encoded by `q0`) is itself
retained in `Q_k`. -/
theorem confidence_set_validity :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (n K : ℕ) (δ : ℝ), 0 < n → 0 < δ → δ ≤ 1 →
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
