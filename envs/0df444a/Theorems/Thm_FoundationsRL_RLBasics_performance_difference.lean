-- Prove2me | Theorems.Thm_FoundationsRL_RLBasics_performance_difference
-- name    : FoundationsRL.RLBasics.performance_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:02:40.131309+00:00
-- url     : https://prove2.me/theorems/9529bd35-c236-47a3-962f-b452812c131e
-- title:
--   Lemma 13 — Performance Difference Lemma
-- statement:
--   The Performance Difference Lemma expresses the gap in value between two policies under the *same* MDP as a sum, over layers, of single-step comparisons.
--
--   Fix a finite-horizon episodic MDP $M$, a state $s$, and two randomized non-stationary policies $\pi,\pi' \in \Pi^{\mathrm{rns}}$. The lemma states
--
--   $$V^{M,\pi'}_1(s) - V^{M,\pi}_1(s) = \sum_{h=1}^{H} \mathbb E^{M,\pi}_{s_h}\Big[\textstyle\sum_{a'} \pi'_h(a'\mid s_h)\, Q^{M,\pi'}_h(s_h,a') - \sum_{a} \pi_h(a\mid s_h)\, Q^{M,\pi'}_h(s_h,a)\Big],$$
--
--   where the outer expectation is over the layer-$h$ state $s_h$ reached by **rolling in** with $\pi$ from $s_1=s$ (i.e. the marginal law `stateDist M π s h`), while at each layer the bracketed term compares, at that same state, the expected $Q^{M,\pi'}$-value of an action drawn from $\pi'$ against one drawn from $\pi$. This is the basic "credit assignment" identity of the chapter: it isolates how a single-step change from $\pi$ to $\pi'$ at layer $h$, holding the roll-in fixed, accounts for the total value gap, and is the workhorse behind the error-decomposition arguments for optimism-based algorithms.
--
--   **Formalization Note** Layers are $0$-indexed. `V M π' 0 s` is the book's $V^{M,\pi'}_1(s)$; `stateExp M π s h` is the expectation under the $\pi$-roll-in state marginal at $0$-indexed layer $h$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 85, Lemma 13, Eq. (5.13)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace FoundationsRL.RLBasics

/-- **Lemma 13 (Performance Difference Lemma)** (Foster–Rakhlin, arXiv:2312.16730v1, p. 85,
Lemma 13, Eq. (5.13)): for any `s` and `π, π' ∈ Π^{rns}`, the difference in initial value
between `π'` and `π` under the same MDP `M` decomposes as a sum, over layers, of the
`π`-roll-in expectation of the gap between `π'`'s and `π`'s single-step choice, both scored
by `Q^{M,π'}`. -/
theorem performance_difference {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq S] [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) (π π' : Policy S A H)
    (hπ : IsPolicy H π) (hπ' : IsPolicy H π') (s : S) :
    V M π' 0 s - V M π 0 s =
      ∑ h ∈ Finset.range H,
        stateExp M π s h (fun sh =>
          (∑ a' : A, π' h sh a' * Q M π' h sh a') -
            ∑ a : A, π h sh a * Q M π' h sh a) := by sorry

end FoundationsRL.RLBasics
