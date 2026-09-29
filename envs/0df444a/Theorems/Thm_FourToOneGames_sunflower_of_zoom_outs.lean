-- Prove2me | Theorems.Thm_FourToOneGames_sunflower_of_zoom_outs
-- name    : FourToOneGames.sunflower_of_zoom_outs
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T23:36:08.511835+00:00
-- url     : https://prove2.me/theorems/8fc64a6f-f949-4a93-95df-27d622d3d3ac
-- title:
--   Lemma 3.8 — a large collection of zoom-outs contains a sunflower
-- statement:
--   A sunflower lemma for subspaces of fixed codimension, used to handle large collections of zoom-outs in the soundness analysis.
--
--   Let $W_1, \dots, W_N \subseteq \mathbb{F}_2^n$ be distinct subspaces of codimension $r \ge 1$, and let $m \ge 1$ satisfy $(m \cdot 2^r)^r \le N$. Then there are $s$ with $1 \le s \le r$, a subspace $W$ of codimension $r - s$, and $m$ of the $W_i$ — say $W_{i_1}, \dots, W_{i_m}$ — all contained in $W$, each of codimension $s$ inside $W$, and with $\mathrm{codim}_W(W_{i_a} \cap W_{i_b}) = 2s$ for all $a \ne b$. Such a configuration is called a sunflower (Definition 3.7 of the source).
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 17, Lemma 3.8 (attributed there to [DKK+ 25]); Definition 3.7, p. 17

import Definitions.Def_FourToOneGames_Grassmann

namespace FourToOneGames

theorem sunflower_of_zoom_outs (n r m N : ℕ) (hr : 0 < r) (hm : 0 < m)
    (W : Fin N → Submodule (ZMod 2) (Fspace n)) (hinj : Function.Injective W)
    (hcodim : ∀ i, codim (W i) = r) (hN : (m * 2 ^ r) ^ r ≤ N) :
    ∃ (s : ℕ) (W₀ : Submodule (ZMod 2) (Fspace n)) (I : Finset (Fin N)),
      0 < s ∧ s ≤ r ∧ codim W₀ = r - s ∧ I.card = m ∧
      (∀ i ∈ I, W i ≤ W₀) ∧
      (∀ i ∈ I, relCodim W₀ (W i) = s) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → relCodim W₀ (W i ⊓ W j) = 2 * s) := by
  sorry

end FourToOneGames
