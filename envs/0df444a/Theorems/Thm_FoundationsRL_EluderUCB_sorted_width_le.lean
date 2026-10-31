-- Prove2me | Theorems.Thm_FoundationsRL_EluderUCB_sorted_width_le
-- name    : FoundationsRL.EluderUCB.sorted_width_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:38.734556+00:00
-- url     : https://prove2.me/theorems/e813be16-1316-4608-bc14-49620f56cef9
-- title:
--   Proof of Proposition 12 — the width at the $\tau$-th largest index
-- statement:
--   In the setting of (4.14), let $\varepsilon>0$ and let $\tau$ be an index with $w^{i_\tau}(\pi^{i_\tau})>\varepsilon$. Then
--
--   $$
--   w^{i_\tau}(\pi^{i_\tau})\le\sqrt{\frac{5\beta\,\mathrm{Edim}(\mathcal F,\varepsilon)}{\tau}}.
--   $$
--
--   Summing this over $\tau$ gives the main term of the regret bound.
--
--   **Formalization Note** The right side is in $[0,\infty]$ and is infinite, so the bound says nothing, when the eluder dimension is infinite.
--
--   Differences from the source: none.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 12, display after (4.14), p. 61

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_edim
import Definitions.Def_FoundationsRL_EluderUCB_width

open scoped ENNReal

namespace FoundationsRL.EluderUCB

/-- **The width at the `τ`-th largest index.** Foster & Rakhlin, arXiv:2312.16730v1, proof of
Proposition 12, p. 61, display after (4.14). With the indices ordered as in (4.14), for any `τ` with
`w^{i_τ}(π^{i_τ}) > ε`, one has `w^{i_τ}(π^{i_τ}) ≤ √(5β Edim(F, ε)/τ)`.

**Formalization Note.** `wᵗ` is `width` with parameter `4β`. The class has values in `[0, 1]` and
contains `f⋆`, so the width's `toReal` loses nothing. The right side is in `ℝ≥0∞` and is `⊤`, so the
bound is vacuous, when `Edim(F, ε) = ⊤`. -/
theorem sorted_width_le {Act : Type*} (F : Set (Act → ℝ))
    (hF : ∀ f ∈ F, ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (fstar : Act → ℝ) (hfstar : fstar ∈ F)
    (β : ℝ) (hβ : 1 ≤ β) (T : ℕ) (π : ℕ → Act)
    (i : ℕ → ℕ) (hi : Set.BijOn i (Finset.Icc 1 T) (Finset.Icc 1 T))
    (hmono : ∀ τ ∈ Finset.Icc 1 T, ∀ τ' ∈ Finset.Icc 1 T, τ ≤ τ' →
      width F fstar (4 * β) π (i τ') (π (i τ')) ≤ width F fstar (4 * β) π (i τ) (π (i τ)))
    (τ : ℕ) (hτ : τ ∈ Finset.Icc 1 T) (ε : ℝ) (hε : 0 < ε)
    (hw : (ε : EReal) < width F fstar (4 * β) π (i τ) (π (i τ))) :
    ENNReal.ofReal (width F fstar (4 * β) π (i τ) (π (i τ))).toReal ≤
      (ENNReal.ofReal (5 * β) * (edim F ε : ℝ≥0∞) / (τ : ℝ≥0∞)) ^ (1 / 2 : ℝ) := by sorry

end FoundationsRL.EluderUCB
