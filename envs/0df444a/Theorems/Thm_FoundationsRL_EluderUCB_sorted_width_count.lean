-- Prove2me | Theorems.Thm_FoundationsRL_EluderUCB_sorted_width_count
-- name    : FoundationsRL.EluderUCB.sorted_width_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:13.936411+00:00
-- url     : https://prove2.me/theorems/2506c959-416b-4a2e-a58d-dbc2a8c8c7b2
-- title:
--   (4.14) — the $\tau$-th largest width and the eluder dimension
-- statement:
--   Let $\mathcal F$ have values in $[0,1]$, let $f^\star\in\mathcal F$ and $\beta\ge1$, and let $w^t$ be the width with parameter $4\beta$ along a sequence $\pi^1,\dots,\pi^T$. Order $\{1,\dots,T\}$ as $\{i_1,\dots,i_T\}$ so that $w^{i_1}(\pi^{i_1})\ge w^{i_2}(\pi^{i_2})\ge\dots$. If $\alpha>0$ and $w^{i_\tau}(\pi^{i_\tau})>\alpha$, then
--
--   $$
--   \tau\le\sum_{t=1}^T\mathbb I\{w^t(\pi^t)>\alpha\}\le\Bigl(\frac{4\beta}{\alpha^2}+1\Bigr)\underline{\mathrm{Edim}}_{f^\star}(\mathcal F,\alpha)\le\frac{5\beta}{\alpha^2}\underline{\mathrm{Edim}}_{f^\star}(\mathcal F,\alpha).
--   $$
--
--   This is the step that turns the count of Lemma 12 into a bound on each sorted width.
--
--   Differences from the source:
--   - generalization: $\alpha>\varepsilon$ for a fixed $\varepsilon>0$, with $\alpha\le1$ noted → any $\alpha>0$ with $w^{i_\tau}(\pi^{i_\tau})>\alpha$; reason: $\varepsilon$ plays no role in the display, and $\alpha\le1$ follows from the width being at most $1$
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.14), p. 61

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_edimRaw
import Definitions.Def_FoundationsRL_EluderUCB_width

open scoped ENNReal Classical

namespace FoundationsRL.EluderUCB

/-- **(4.14).** Foster & Rakhlin, arXiv:2312.16730v1, (4.14), p. 61. Order `{1, …, T}` as
`i₁, …, i_T` so that `w^{i₁}(π^{i₁}) ≥ w^{i₂}(π^{i₂}) ≥ …`. If `w^{i_τ}(π^{i_τ}) > α`, then (since
`α ≤ 1 ≤ β`)
`τ ≤ ∑_{t=1}^T I{wᵗ(πᵗ) > α} ≤ (4β/α² + 1) Edim̲_{f⋆}(F, α) ≤ (5β/α²) Edim̲_{f⋆}(F, α)`.

**Formalization Note.** `wᵗ` is `width` with parameter `4β`. The ordering is a bijection `i` of
`{1, …, T}`. `α ≤ 1` is not a hypothesis: it follows from `α < w^{i_τ}(π^{i_τ}) ≤ 1`, since the class
has values in `[0, 1]`. The source's scale `ε < α` plays no role in this display and is not carried.
The chain is in `ℝ≥0∞`, so it is vacuous when `edimRaw` is `⊤`. -/
theorem sorted_width_count {Act : Type*} (F : Set (Act → ℝ))
    (hF : ∀ f ∈ F, ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (fstar : Act → ℝ) (hfstar : fstar ∈ F)
    (β : ℝ) (hβ : 1 ≤ β) (T : ℕ) (π : ℕ → Act)
    (i : ℕ → ℕ) (hi : Set.BijOn i (Finset.Icc 1 T) (Finset.Icc 1 T))
    (hmono : ∀ τ ∈ Finset.Icc 1 T, ∀ τ' ∈ Finset.Icc 1 T, τ ≤ τ' →
      width F fstar (4 * β) π (i τ') (π (i τ')) ≤ width F fstar (4 * β) π (i τ) (π (i τ)))
    (τ : ℕ) (hτ : τ ∈ Finset.Icc 1 T) (α : ℝ) (hα : 0 < α)
    (hw : (α : EReal) < width F fstar (4 * β) π (i τ) (π (i τ))) :
    (τ : ℝ≥0∞) ≤ ∑ t ∈ Finset.Icc 1 T,
        (if (α : EReal) < width F fstar (4 * β) π t (π t) then (1 : ℝ≥0∞) else 0) ∧
      ∑ t ∈ Finset.Icc 1 T,
          (if (α : EReal) < width F fstar (4 * β) π t (π t) then (1 : ℝ≥0∞) else 0) ≤
        ENNReal.ofReal (4 * β / α ^ 2 + 1) * (edimRaw F fstar α : ℝ≥0∞) ∧
      ENNReal.ofReal (4 * β / α ^ 2 + 1) * (edimRaw F fstar α : ℝ≥0∞) ≤
        ENNReal.ofReal (5 * β / α ^ 2) * (edimRaw F fstar α : ℝ≥0∞) := by sorry

end FoundationsRL.EluderUCB
