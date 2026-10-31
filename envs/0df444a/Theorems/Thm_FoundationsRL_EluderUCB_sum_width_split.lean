-- Prove2me | Theorems.Thm_FoundationsRL_EluderUCB_sum_width_split
-- name    : FoundationsRL.EluderUCB.sum_width_split
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:20:33.609244+00:00
-- url     : https://prove2.me/theorems/3594b3cf-cbdd-43da-aaea-0ee3a2e1faad
-- title:
--   (4.13) — splitting the widths at scale $\varepsilon$
-- statement:
--   Let $\mathcal F$ have values in $[0,1]$, let $f^\star\in\mathcal F$, $\beta\ge0$ and $\varepsilon>0$, and let $w^t$ be the width with parameter $4\beta$ along a sequence $\pi^1,\dots,\pi^T$. Then
--
--   $$
--   \sum_{t=1}^T w^t(\pi^t)\le\sum_{t=1}^T w^t(\pi^t)\,\mathbb I\{w^t(\pi^t)>\varepsilon\}+\varepsilon T.
--   $$
--
--   Rounds with small width cost at most $\varepsilon$ each, and the remaining rounds are handled with Lemma 12.
--
--   Differences from the source: none.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.13), p. 61

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_width

open scoped Classical

namespace FoundationsRL.EluderUCB

/-- **(4.13).** Foster & Rakhlin, arXiv:2312.16730v1, (4.13), p. 61. For `ε > 0`,
`∑_{t=1}^T wᵗ(πᵗ) ≤ ∑_{t=1}^T wᵗ(πᵗ) I{wᵗ(πᵗ) > ε} + εT`, for the widths of the proof of
Proposition 12.

**Formalization Note.** `wᵗ` is `width` with parameter `4β`. The class has values in `[0, 1]` and
contains `f⋆`, and `β ≥ 0`, so every width lies in `[0, 1]` and `EReal.toReal` loses nothing. -/
theorem sum_width_split {Act : Type*} (F : Set (Act → ℝ))
    (hF : ∀ f ∈ F, ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (fstar : Act → ℝ) (hfstar : fstar ∈ F)
    (β : ℝ) (hβ : 0 ≤ β) (T : ℕ) (π : ℕ → Act) (ε : ℝ) (hε : 0 < ε) :
    ∑ t ∈ Finset.Icc 1 T, (width F fstar (4 * β) π t (π t)).toReal ≤
      ∑ t ∈ Finset.Icc 1 T, ((width F fstar (4 * β) π t (π t)).toReal *
        (if ε < (width F fstar (4 * β) π t (π t)).toReal then 1 else 0)) + ε * T := by sorry

end FoundationsRL.EluderUCB
