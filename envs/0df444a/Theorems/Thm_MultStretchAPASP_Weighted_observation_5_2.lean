-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_observation_5_2
-- name    : MultStretchAPASP.Weighted.observation_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:09:27.404058+00:00
-- url     : https://prove2.me/theorems/b42ac84b-67d1-4b96-83e8-1e259229496c
-- title:
--   Observation 5.2 — Algorithm 9 does not underestimate any entry of M₁ ⋆ M₂
-- statement:
--   Let $M_1$ be an $l_1\times l_2$ and $M_2$ an $l_2\times l_3$ matrix with entries in $[0,\infty]$, $\mathrm{off}_1,\mathrm{off}_2\ge0$ and $\varepsilon>0$, and assume the input is correct: every entry of $M_1$ is at least $\mathrm{off}_1$ and every entry of $M_2$ at least $\mathrm{off}_2$. Then every possible output $M$ of Algorithm 9, $\textsc{Offset\_Shifted\_AMPMM}(M_1,M_2,\mathrm{off}_1,\mathrm{off}_2,\varepsilon)$, satisfies
--   $$M[i,j]\ \ge\ (M_1\star M_2)[i,j]\qquad\text{for every entry }(i,j).$$
--
--   This is the lower-bound half of the correctness of the offset-shifted product, the new tool of §5; Lemma 5.4 uses it for line 24 of Algorithm 10.
--
--   Differences from the source:
--
--   - encoding: an l₁ × l₂ matrix M₁ and an l₂ × l₃ matrix M₂ → functions M₁ : α → ι → ℝ≥0∞, M₂ : ι → β → ℝ≥0∞ on finite index sets R ⊆ α, K ⊆ ι, C ⊆ β; entries outside R × K, K × C are never read; reason: any finite index sets; ℝ≥0∞ holds the +∞ entries of Definition 2.13
--   - encoding: a value offset_i with each entry of M_i at least offset_i → off_i : ℝ≥0 with hypotheses (off_i : ℝ≥0∞) ≤ M_i on the relevant entries; reason: the shifts of Algorithm 10 are non-negative
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 20, Observation 5.2

import Mathlib
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus

set_option autoImplicit false

open scoped ENNReal NNReal

namespace MultStretchAPASP.Weighted

/-- **Observation 5.2** (p. 20). If every entry of `M₁` (on `R × K`) is at least `off₁` and every
entry of `M₂` (on `K × C`) is at least `off₂` ("the input is correct"), then every possible output
`M` of Algorithm 9, `Offset_Shifted_AMPMM(M₁, M₂, off₁, off₂, ε)` with `ε > 0`, satisfies
`M[x, y] ≥ (M₁ ⋆ M₂)[x, y]` for every entry `(x, y) ∈ R × C`. -/
theorem observation_5_2 {α ι β : Type} (ε : ℝ) (hε : 0 < ε) (R : Finset α) (K : Finset ι)
    (C : Finset β) (M₁ : α → ι → ℝ≥0∞) (M₂ : ι → β → ℝ≥0∞) (off₁ off₂ : ℝ≥0)
    (h₁ : ∀ x ∈ R, ∀ k ∈ K, (off₁ : ℝ≥0∞) ≤ M₁ x k)
    (h₂ : ∀ k ∈ K, ∀ y ∈ C, (off₂ : ℝ≥0∞) ≤ M₂ k y)
    (M : α → β → ℝ≥0∞) (hM : IsOffsetShiftedOut ε R K C M₁ M₂ off₁ off₂ M) :
    ∀ x ∈ R, ∀ y ∈ C, minPlus K M₁ M₂ x y ≤ M x y := by sorry

end MultStretchAPASP.Weighted
