-- Prove2me | Theorems.Thm_FoundationsRL_LinUCB_epsilon_net_unit_ball
-- name    : FoundationsRL.LinUCB.epsilon_net_unit_ball
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:17.28165+00:00
-- url     : https://prove2.me/theorems/593fab38-3ebf-4625-ac58-c2b6e363206b
-- title:
--   §3.2, p. 43 — $\varepsilon$-nets of subsets of the unit ball have size at most $(3/\varepsilon)^d$
-- statement:
--   Let $\Theta\subseteq B_2^d(1)$ and $\varepsilon\in(0,1]$. Then there is a finite set $N\subseteq\Theta$ with
--
--   $$
--   |N|\le(3/\varepsilon)^d
--   $$
--
--   such that every $\theta\in\Theta$ is within Euclidean distance $\varepsilon$ of some $\theta'\in N$.
--
--   This is the covering estimate behind the extension of Proposition 7 to infinite classes: at $\varepsilon\sim1/T$ it gives $\log|N|\lesssim d\log T$.
--
--   Differences from the source:
--   - reading: "of size at most $O(\varepsilon^{-d})$" → an explicit bound $(3/\varepsilon)^d$ for $\varepsilon\in(0,1]$; reason: the use $\log|\mathcal F|\lesssim d\log T$ requires a constant of the form $C^d$, and no bound of this form can hold for large $\varepsilon$ on a nonempty set.
--   - encoding: Euclidean distance → $(\theta-\theta')\cdot(\theta-\theta')\le\varepsilon^2$; reason: vectors are `Fin d → ℝ` with the dot product.
--   - reading: an $\varepsilon$-net of $\Theta$ → a net $N\subseteq\Theta$; reason: the net is used to discretize the class, so its functions must stay in the class and in $[0,1]$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §3.2, p. 43

import Mathlib

open Matrix

namespace FoundationsRL.LinUCB

/-- The covering bound of §3.2 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 43): every `Θ ⊆ B^d_2(1)` has, for `ε ∈ (0, 1]`, an `ε`-net
`N ⊆ Θ` of size at most `(3/ε)^d`, the book's "of size at most `O(ε^{−d})`".

**Formalization Note.** The book leaves the constant in `O(ε^{−d})` open. It must be of the form
`C^d`, for `log|N| ≲ d log T` at `ε ∼ 1/T`, so an explicit base is stated. The net lies inside `Θ`,
which keeps its functions in the class and in `[0, 1]`. -/
theorem epsilon_net_unit_ball {d : ℕ} (Θ : Set (Fin d → ℝ)) (hΘ : ∀ θ ∈ Θ, θ ⬝ᵥ θ ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset (Fin d → ℝ), (N : Set (Fin d → ℝ)) ⊆ Θ ∧ (N.card : ℝ) ≤ (3 / ε) ^ d ∧
      ∀ θ ∈ Θ, ∃ θ' ∈ N, (θ - θ') ⬝ᵥ (θ - θ') ≤ ε ^ 2 := by sorry

end FoundationsRL.LinUCB
