-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_D_3
-- name    : OnlineBinCover.lemma_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:11.848203+00:00
-- url     : https://prove2.me/theorems/ea7cc677-562b-468a-96ac-a8ba541bbcc6
-- title:
--   Lemma D.3 — the initial epochs hold at most $2n/\mathrm{vol}(I)^{1/20}$ items
-- statement:
--   For every arrival order and every instance $I$ of $n$ items with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge1$, the initial epochs $E_1,\dots,E_j$ of Algorithm 4 contain at most
--
--   $$\frac{2n}{\mathrm{vol}(I)^{1/20}}$$
--
--   items in total, i.e. $\min(n_j,n)\le2n/\mathrm{vol}(I)^{1/20}$.
--
--   The items not used by the later epochs are therefore a vanishing fraction of the input.
--
--   Differences from the source:
--   - generalization: $\mathrm{vol}(I)$ sufficiently large (standing in App. D.2, p.34) → $\mathrm{vol}(I)\ge1$; reason: the bound holds for every such instance; specializes
--   - encoding: the number of items of the initial epochs → $\min(n_j,n)$; reason: the epochs fill positions $1,\dots,n_j$, cut at $n$
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma D.3, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_OnlineBinCover_Epochs

namespace OnlineBinCover

/-- Lemma D.3, p.35. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

For every arrival order and every instance with sizes in `(0,1]` and `vol(I) ≥ 1`, the initial epochs
`E_1, …, E_j` of Algorithm 4 contain at most `2n / vol(I)^{1/20}` items in total. -/
theorem lemma_D_3 {n : ℕ} (s : Fin n → ℝ) (hs : ValidSizes s) (hv : 1 ≤ vol s)
    (σ : Equiv.Perm (Fin n)) :
    ((min (epEnd (s ∘ σ) (jInit (s ∘ σ))) n : ℕ) : ℝ) ≤ 2 * (n : ℝ) / vol s ^ ((1 : ℝ) / 20) := by sorry

end OnlineBinCover
