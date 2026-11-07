-- Prove2me | Theorems.Thm_MemoryRegret_theorem_12_no_case_mistakes
-- name    : MemoryRegret.theorem_12_no_case_mistakes
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:14.766242+00:00
-- url     : https://prove2.me/theorems/f528f4fc-2dc4-40a8-8da0-4288e6ecd1fb
-- title:
--   Theorem 12 — the NO case forces many mistakes
-- statement:
--   Let $\epsilon>0$, $m,T_{\mathrm{block}}\in\mathbb N$, $T=mT_{\mathrm{block}}$ and let $\mu$ be a distribution on $X$. Draw $T_{\mathrm{block}}$ elements $(x_{t'},b_{t'})$ from $D_0$ (Definition 3) and present them as $T$ labeled examples, the element $(x_{t'},b_{t'})$ giving the $m$ consecutive examples $(x_{t'},b_{t'}^{(i)})$. If
--   $$m\le\frac1{160^2\epsilon^2}\quad\text{and}\quad\exp(-T\epsilon^2/128)\le\frac1{10},$$
--   then the number of mistakes $M$ of every (possibly randomized) online learning algorithm satisfies
--   $$\Pr\Bigl(M\ge T\Bigl(\frac12-\frac\epsilon4\Bigr)\Bigr)\ge\frac45.$$
--
--   So in the NO case of the distinguishing problem no learner, however much memory it has, does noticeably better than random guessing.
--
--   **Formalization Note** The hypotheses force $m\ge1$ and $\epsilon\le1/160$, so $D_0$ is a distribution.
--
--   Differences from the source:
--   - encoding: (t′, i) ∈ [T_block] × [m] and t = (t′ − 1)m + i → 0-based rounds t = t′·m + i; reason: the same flattening
--   - encoding: m ≤ 1/(160²ϵ²) → m·160²ϵ² ≤ 1; reason: multiplicative form avoids x/0 = 0; ϵ > 0 makes them equivalent
--   - encoding: any (possibly randomized) online learning algorithm → a finite-seed mixture of deterministic algorithms that see all past examples and the current instance, with no memory bound; reason: with finite X and a finite horizon every such algorithm has this form
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Theorem 12, p.34

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_RandOnlineAlg

namespace MemoryRegret

/-- **Theorem 12 (the NO case forces many mistakes).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Theorem 12, p.34.

Let `ϵ > 0`, `m, T_block ∈ ℕ`, `T = m·T_block`, and `µ` a distribution on the finite set `X`.
Draw `T_block` elements `(x_{t′}, b_{t′})` from `D_0` (Definition 3) and present them as the
sequence of `T` labeled examples with round `t = t′·m + i` equal to `(x_{t′}, b_{t′}^{(i)})`.
If `m ≤ 1/(160²ϵ²)` and `exp(−Tϵ²/128) ≤ 1/10`, then every (possibly randomized) online
learning algorithm makes `M ≥ T(½ − ϵ/4)` mistakes with probability at least `4/5`.

**Formalization Note.** `1/(160²ϵ²)` is written multiplicatively. The hypotheses force `m ≥ 1`
(else `T = 0` and `exp(0) = 1 > 1/10`) and then `ϵ ≤ 1/160`, so `D_0` is a distribution. The
algorithm sees all past examples and the current instance and has no memory bound
(`RandOnlineAlg`). Rounds are 0-based. -/
theorem theorem_12_no_case_mistakes {X : Type} [Fintype X] (μ : X → ℝ) (hμ : IsProbVec μ)
    (ϵ : ℝ) (hϵ : 0 < ϵ) (m Tb : ℕ) (hm : (m : ℝ) * (160 ^ 2 * ϵ ^ 2) ≤ 1)
    (hexp : Real.exp (-((m * Tb : ℕ) * ϵ ^ 2) / 128) ≤ 1 / 10)
    {Ω : Type} [Fintype Ω] (A : RandOnlineAlg X (m * Tb) Ω) :
    4 / 5 ≤ ∑ s : Fin Tb → X × (Fin m → Bool), streamD0 μ ϵ s *
      wprob A.seedLaw (fun ω => ((m * Tb : ℕ) : ℝ) * (1 / 2 - ϵ / 4) ≤
        A.algMistakes ω (flattenStream s)) := by sorry

end MemoryRegret
