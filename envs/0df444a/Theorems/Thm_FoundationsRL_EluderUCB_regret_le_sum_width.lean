-- Prove2me | Theorems.Thm_FoundationsRL_EluderUCB_regret_le_sum_width
-- name    : FoundationsRL.EluderUCB.regret_le_sum_width
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:44.165777+00:00
-- url     : https://prove2.me/theorems/981c9b54-dd12-4883-a199-9575c7350103
-- title:
--   Proof of Proposition 12 — the regret is at most the sum of the widths
-- statement:
--   Let $\mathcal F$ be a finite class with values in $[0,1]$ and consider a run of generalized UCB with parameter $\beta$. Suppose that for all $t\in[T]$ we have $f^\star\in\mathcal F^t$ and $\mathcal F^t\subseteq\overline{\mathcal F}^t$, where
--
--   $$
--   \overline{\mathcal F}^t=\Bigl\{f\in\mathcal F:\ \sum_{i<t}\bigl(f(\pi^i)-f^\star(\pi^i)\bigr)^2\le4\beta\Bigr\}.
--   $$
--
--   Then, with $w^t(\pi)=\sup_{f\in\overline{\mathcal F}^t}[f(\pi)-f^\star(\pi)]$,
--
--   $$
--   \mathrm{Reg}\le\sum_{t=1}^T w^t(\pi^t).
--   $$
--
--   This replaces the data-dependent confidence set by the deterministic constraint to which Lemma 12 applies.
--
--   Differences from the source: none.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 12, pp. 60–61

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_regret
import Definitions.Def_FoundationsRL_EluderUCB_IsGeneralizedUCBRun
import Definitions.Def_FoundationsRL_EluderUCB_width

namespace FoundationsRL.EluderUCB

/-- **The regret is at most the sum of the widths.** Foster & Rakhlin, arXiv:2312.16730v1, proof of
Proposition 12, pp. 60–61. If `f⋆ ∈ Fᵗ` and `Fᵗ ⊆ F̄ᵗ := {f ∈ F : ∑_{i<t} (f(πⁱ) - f⋆(πⁱ))² ≤ 4β}` for
all `t`, then `Reg ≤ ∑_{t=1}^T wᵗ(πᵗ)`, with `wᵗ(π) = sup_{f ∈ F̄ᵗ} [f(π) - f⋆(π)]`.

**Formalization Note.** `F̄ᵗ` is written out and `wᵗ` is `width` with parameter `4β`. The class has
values in `[0, 1]` and contains `f⋆`, so every width lies in `[0, 1]` and `EReal.toReal` loses
nothing. -/
theorem regret_le_sum_width {Act : Type*} (F : Set (Act → ℝ)) (hfin : F.Finite)
    (hF : ∀ f ∈ F, ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (β : ℝ)
    (fstar : Act → ℝ) (T : ℕ) (π : ℕ → Act) (r : ℕ → ℝ) (fhat : ℕ → Act → ℝ)
    (hrun : IsGeneralizedUCBRun F β T π r fhat)
    (hmem : ∀ t ∈ Finset.Icc 1 T, fstar ∈ confidenceSet F β π r t (fhat t))
    (hsub : ∀ t ∈ Finset.Icc 1 T, ∀ f ∈ confidenceSet F β π r t (fhat t),
      ∑ i ∈ Finset.Ico 1 t, (f (π i) - fstar (π i)) ^ 2 ≤ 4 * β) :
    regret fstar T π ≤ ∑ t ∈ Finset.Icc 1 T, (width F fstar (4 * β) π t (π t)).toReal := by sorry

end FoundationsRL.EluderUCB
