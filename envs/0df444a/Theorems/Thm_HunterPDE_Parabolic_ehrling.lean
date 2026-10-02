-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_ehrling
-- name    : HunterPDE.Parabolic.ehrling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:17:57.080668+00:00
-- url     : https://prove2.me/theorems/df2ea38a-4b77-449b-9cfe-a133022ea063
-- title:
--   Lemma 6.10 — Ehrling's lemma
-- statement:
--   Let $X \hookrightarrow Y \hookrightarrow Z$ be real Banach spaces, the embeddings $i : X \to Y$ and $j : Y \to Z$ being continuous injective linear maps, and suppose that $X$ is compactly embedded in $Y$ ($i$ is a compact operator). Then for every $\varepsilon > 0$ there is a constant $C_\varepsilon$ such that
--   $$\|u\|_Y \le \varepsilon\,\|u\|_X + C_\varepsilon\,\|u\|_Z \qquad \text{for all } u \in X.$$
--
--   The lemma is the interpolation step behind the Aubin–Lions compactness theorem (Theorem 6.9).
--
--   **Formalization Note.** $\|u\|_Y$ is `‖i u‖` and $\|u\|_Z$ is `‖j (i u)‖`. $C_\varepsilon$ is quantified after $\varepsilon$ and before $u$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 190, Lemma 6.10

import Mathlib

namespace HunterPDE.Parabolic

/-- Lemma 6.10 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 190 (Ehrling's lemma): let
`X ↪ Y ↪ Z` be Banach spaces, the embeddings being continuous injective linear maps
`i : X → Y`, `j : Y → Z`, with `X` compactly embedded in `Y` (`i` is a compact operator). Then
for every `ε > 0` there is a constant `C_ε` such that `‖u‖_Y ≤ ε ‖u‖_X + C_ε ‖u‖_Z` for all
`u ∈ X`. The constant `C_ε` is quantified before `u`. -/
theorem ehrling {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (i : X →L[ℝ] Y) (j : Y →L[ℝ] Z) (hi : Function.Injective i) (hj : Function.Injective j)
    (hcpt : IsCompactOperator i) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ u : X, ‖i u‖ ≤ ε * ‖u‖ + Cε * ‖j (i u)‖ := by sorry

end HunterPDE.Parabolic
