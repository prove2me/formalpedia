-- Prove2me | Theorems.Thm_FoundationsRL_EluderUCB_regret_le_upper_confidence_width
-- name    : FoundationsRL.EluderUCB.regret_le_upper_confidence_width
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:39.246141+00:00
-- url     : https://prove2.me/theorems/0f214aea-e0d4-4cab-be0b-011cab72fa2e
-- title:
--   (4.7) — regret is bounded by the upper confidence width
-- statement:
--   Let $\mathcal F$ be a finite class and consider a run of generalized UCB with parameter $\beta$ over $T$ rounds. If $f^\star\in\mathcal F^t$ for all $t\in[T]$, then
--
--   $$
--   \mathrm{Reg}\le\sum_{t=1}^T\bigl(\bar f^t(\pi^t)-f^\star(\pi^t)\bigr).
--   $$
--
--   This is the optimism step: it holds on a fixed sample path and needs no structure on $\Pi$ or $\mathcal F$. The remaining task of the analysis is to show that the confidence widths shrink.
--
--   **Formalization Note** The platform's optimism lemma `FoundationsRL.Bandits.optimism_lemma` is stated for finitely many decisions, so this statement carries the step for an arbitrary $\Pi$.
--
--   Differences from the source:
--   - encoding: $\mathcal F$ arbitrary and the maxima $\bar f^t$ presupposed → $\mathcal F$ finite; reason: finiteness is what makes the maxima exist, and it is the setting of §4.1.1, where $\beta=8\log(|\mathcal F|/\delta)$ presupposes a finite class
--   - generalization: $\mathcal F\subset(\Pi\to[0,1])$, $\beta=8\log(|\mathcal F|/\delta)$ (standing assumptions of §4.1.1) → real-valued $\mathcal F$ and any real $\beta$; reason: the optimism step uses only $f^\star\in\mathcal F^t$ and the maximality of $\pi^t$, so the source's case is a special case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.7), p. 58

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_regret
import Definitions.Def_FoundationsRL_EluderUCB_IsGeneralizedUCBRun

namespace FoundationsRL.EluderUCB

/-- **(4.7): regret is bounded by the upper confidence width.** Foster & Rakhlin,
arXiv:2312.16730v1, (4.7), p. 58. Whenever `f⋆ ∈ Fᵗ` for all `t`, the generalized UCB algorithm has
`Reg ≤ ∑_{t=1}^T (f̄ᵗ(πᵗ) - f⋆(πᵗ))`. The bound holds on a fixed sample path, with no assumption on
the structure of `Π` and `F` beyond the finiteness of `F`, which makes the maxima `f̄ᵗ` exist.

**Formalization Note.** The source's optimism Lemma 7 (`FoundationsRL.Bandits.optimism_lemma`) is
stated on `Fin A`, so it does not apply to an arbitrary `Π`; this statement carries the same step. -/
theorem regret_le_upper_confidence_width {Act : Type*} (F : Set (Act → ℝ)) (hfin : F.Finite)
    (β : ℝ) (fstar : Act → ℝ) (T : ℕ) (π : ℕ → Act) (r : ℕ → ℝ) (fhat : ℕ → Act → ℝ)
    (hrun : IsGeneralizedUCBRun F β T π r fhat)
    (hmem : ∀ t ∈ Finset.Icc 1 T, fstar ∈ confidenceSet F β π r t (fhat t)) :
    regret fstar T π ≤
      ∑ t ∈ Finset.Icc 1 T, (ucbIndex F β π r t (fhat t) (π t) - fstar (π t)) := by sorry

end FoundationsRL.EluderUCB
