-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_5_9
-- name    : ImplicitParityWL.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:28.203713+00:00
-- url     : https://prove2.me/theorems/908bf9ad-97fa-4f2c-a8af-1694460af21d
-- title:
--   Lemma 5.9 — exposure bounds
-- statement:
--   Let $\mathcal A$ be a set of colors.
--
--   1. If $|\mathcal A|\le k+1$, then $\mathrm{Var}(\mathcal A)$ contains at most one variable per location, $|\mathrm{Var}(\mathcal A)|\le4$ and $|\mathrm{Eqs}(\mathcal A)|\le1$.
--   2. If $|\mathcal A|\le k$, then $|h\cap\mathrm{Var}(\mathcal A)|\le1$ for every equation $h$ newly exposed by adding one color $A$ to $\mathcal A$, i.e., for $h\notin\mathrm{Eqs}(\mathcal A)$ with $h\in\mathrm{Eqs}(\mathcal A\cup\{A\})$.
--
--   This is where clause (iii) of Definition 4.9 enters: distinct schemas share at most one location.
--
--   Differences from the source:
--   - encoding: a set of colors 𝒜 → a Finset of color names (`CColor`), where a name that is no color class of the compiled graphs (a `sum` color of a binary schema, a track index outside [1, k+1], a coordinate outside the domain) adds no coordinate; reason: such names select no vertex, so they change no I_v, I_e, Var or Eqs
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 5.9, p.30

import Mathlib
import Definitions.Def_ImplicitParityWL_Exposure

namespace ImplicitParityWL

/-- **Lemma 5.9** (Exposure; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.30): let `A` be a set of colors. (i) If `|A| ≤ k + 1`, then `Var(A)` contains at most
one variable per location, `|Var(A)| ≤ 4` and `|Eqs(A)| ≤ 1`. (ii) If `|A| ≤ k`, then `|h ∩ Var(A)| ≤ 1` for every equation
`h` newly exposed by adding one color `A₀` to `A`, i.e., for `h ∉ Eqs(A)` with `h ∈ Eqs(A ∪ {A₀})`. -/
theorem lemma_5_9 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) {W E : Type} [Fintype W] [Fintype E]
    [DecidableEq (CColor k ℓ W E)] (I : ImplicitSystem k ℓ W E) (A : Finset (CColor k ℓ W E)) :
    (A.card ≤ k + 1 →
      (∀ (v : W) (a a' : Address k ℓ), (v, a) ∈ I.Var A → (v, a') ∈ I.Var A → a = a') ∧
      (I.Var A).encard ≤ 4 ∧ (I.Eqs A).encard ≤ 1) ∧
    (A.card ≤ k → ∀ (A₀ : CColor k ℓ W E) (h : Finset (W × Address k ℓ)),
      h ∉ I.Eqs A → h ∈ I.Eqs (insert A₀ A) → ((h : Set (W × Address k ℓ)) ∩ I.Var A).encard ≤ 1) := by sorry

end ImplicitParityWL
