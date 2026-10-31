-- Prove2me | Theorems.Thm_FoundationsRL_EluderUCB_sum_width_le
-- name    : FoundationsRL.EluderUCB.sum_width_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:22.588466+00:00
-- url     : https://prove2.me/theorems/54322fc9-0066-4afe-af10-529dfaf30bca
-- title:
--   Proof of Proposition 12 — the sum of the widths
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $\mathcal F$ have values in $[0,1]$, let $f^\star\in\mathcal F$ and $\beta\ge1$, and let $w^t$ be the width with parameter $4\beta$ along a sequence $\pi^1,\dots,\pi^T$. For every $\varepsilon>0$,
--
--   $$
--   \sum_{t=1}^T w^t(\pi^t)\le C\Bigl(\sqrt{\beta\,\mathrm{Edim}(\mathcal F,\varepsilon)\,T}+\varepsilon T\Bigr).
--   $$
--
--   This is the deterministic core of Proposition 12. Together with the regret bound by the widths and the confidence sets of Lemma 10 it gives (4.10).
--
--   **Formalization Note** The inequality is in $[0,\infty]$, so it says nothing when the eluder dimension is infinite.
--
--   Differences from the source:
--   - reading: $\mathrm{Reg}\lesssim\sqrt{\beta\mathrm{Edim}(\mathcal F,\varepsilon)T}+\varepsilon T$ on the good event → the same right side as a bound on $\sum_t w^t(\pi^t)$ for every sequence; reason: the source bounds the regret through this sum; the sum is the quantity the two preceding displays control
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 12, p. 61

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_edim
import Definitions.Def_FoundationsRL_EluderUCB_width

open scoped ENNReal

namespace FoundationsRL.EluderUCB

universe u

/-- **The sum of the widths.** Foster & Rakhlin, arXiv:2312.16730v1, proof of Proposition 12, p. 61,
last lines: for every `ε > 0`, `∑_{t=1}^T wᵗ(πᵗ) ≲ √(β Edim(F, ε) T) + εT`, for an arbitrary sequence
of decisions and with one absolute constant.

**Formalization Note.** `wᵗ` is `width` with parameter `4β`, and `≲` is an absolute constant `C`,
quantified before the types it is uniform over. The inequality is in `ℝ≥0∞`, so it is vacuous when
`Edim(F, ε) = ⊤` and `T ≥ 1`. The hypothesis `1 ≤ β` is the source's `β ≥ 1`, used at (4.14). -/
theorem sum_width_le : ∃ C : ℝ, 0 < C ∧ ∀ {Act : Type u} (F : Set (Act → ℝ))
    (_ : ∀ f ∈ F, ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (fstar : Act → ℝ) (_ : fstar ∈ F)
    (β : ℝ) (_ : 1 ≤ β) (T : ℕ) (π : ℕ → Act) (ε : ℝ) (_ : 0 < ε),
    ENNReal.ofReal (∑ t ∈ Finset.Icc 1 T, (width F fstar (4 * β) π t (π t)).toReal) ≤
      ENNReal.ofReal C * ((ENNReal.ofReal β * (edim F ε : ℝ≥0∞) * (T : ℝ≥0∞)) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (ε * T)) := by sorry

end FoundationsRL.EluderUCB
