-- Prove2me | Theorems.Thm_FoundationsRL_EluderUCB_lemma_12
-- name    : FoundationsRL.EluderUCB.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:22.611771+00:00
-- url     : https://prove2.me/theorems/1166483b-c119-4d2e-8dfe-87cb53b33d74
-- title:
--   Lemma 12 — counting large widths by the eluder dimension
-- statement:
--   Fix a class $\mathcal F\subset(\Pi\to\mathbb R)$, a function $f^\star\in\mathcal F$ and $\beta>0$. For any deterministic sequence $\pi^1,\dots,\pi^T\in\Pi$, let
--
--   $$
--   w^t(\pi)=\sup_{f\in\mathcal F}\Bigl\{f(\pi)-f^\star(\pi):\ \sum_{i<t}\bigl(f(\pi^i)-f^\star(\pi^i)\bigr)^2\le\beta\Bigr\}.
--   $$
--
--   Then for all $\alpha>0$,
--
--   $$
--   \sum_{t=1}^T\mathbb I\{w^t(\pi^t)>\alpha\}\le\Bigl(\frac{\beta}{\alpha^2}+1\Bigr)\cdot\underline{\mathrm{Edim}}_{f^\star}(\mathcal F,\alpha).
--   $$
--
--   The lemma is purely combinatorial. It shows that the count of large widths is controlled at every scale at once, with a prefactor $\beta/\alpha^2$ when $\alpha^2\ll\beta$.
--
--   **Formalization Note** The dimension is the underlined one of Definition 6, as printed. The inequality is in $[0,\infty]$, so it says nothing when the dimension is infinite.
--
--   Differences from the source: none.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 12, p. 61

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_edimRaw
import Definitions.Def_FoundationsRL_EluderUCB_width

open scoped ENNReal Classical

namespace FoundationsRL.EluderUCB

/-- **Lemma 12** (Russo and Van Roy, Lemma 3). Foster & Rakhlin, arXiv:2312.16730v1, Lemma 12, p. 61.
Fix a class `F`, a function `f⋆ ∈ F` and `β > 0`. For any sequence `π¹, …, πᵀ` and all `α > 0`,
`∑_{t=1}^T I{wᵗ(πᵗ) > α} ≤ (β/α² + 1) · Edim̲_{f⋆}(F, α)`.

**Formalization Note.** The dimension on the right is the underlined one, `edimRaw`, as printed. The
statement is in `ℝ≥0∞`, so it is vacuous when `edimRaw` is `⊤`, and the sequence is deterministic. -/
theorem lemma_12 {Act : Type*} (F : Set (Act → ℝ)) (fstar : Act → ℝ) (hfstar : fstar ∈ F)
    (β : ℝ) (hβ : 0 < β) (T : ℕ) (π : ℕ → Act) (α : ℝ) (hα : 0 < α) :
    ∑ t ∈ Finset.Icc 1 T, (if (α : EReal) < width F fstar β π t (π t) then (1 : ℝ≥0∞) else 0) ≤
      ENNReal.ofReal (β / α ^ 2 + 1) * (edimRaw F fstar α : ℝ≥0∞) := by sorry

end FoundationsRL.EluderUCB
