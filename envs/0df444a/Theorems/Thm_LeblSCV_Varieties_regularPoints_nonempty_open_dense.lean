-- Prove2me | Theorems.Thm_LeblSCV_Varieties_regularPoints_nonempty_open_dense
-- name    : LeblSCV.Varieties.regularPoints_nonempty_open_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:14:18.055155+00:00
-- url     : https://prove2.me/theorems/634582c0-a36c-4c0b-a05a-80f29900692e
-- title:
--   Lemma 6.5.10 — regular points of a subvariety are nonempty, open and dense
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and let $X \subset U$ be a subvariety. If $X \neq \emptyset$, then $X_{\mathrm{reg}} \neq \emptyset$. Consequently $X_{\mathrm{reg}}$ is open and dense in $X$:
--   $$X_{\mathrm{reg}} = O \cap X \text{ for some open } O \subset \mathbb{C}^n, \qquad X \subset \overline{X_{\mathrm{reg}}}.$$
--
--   Regular points are therefore found arbitrarily close to every point of a subvariety; this is what makes the dimension at a singular point (Definition 6.5.7) meaningful.
--
--   **Formalization Note.** The page says "$X_{\mathrm{reg}}$ is nonempty" without the proviso $X \ne \emptyset$, which is needed (for $X = \emptyset$ the claim is false) and is what the proof uses; the nonemptiness clause is stated under that hypothesis. Openness in $X$ is expressed with an ambient open set $O$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 187, Lemma 6.5.10

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsSubvariety
import Definitions.Def_LeblSCV_Varieties_regularPoints

namespace LeblSCV.Varieties

/-- Lebl, Lemma 6.5.10: for a subvariety `X` of an open `U ⊆ ℂⁿ`, `X_reg` is nonempty (when `X`
is nonempty — the page omits this proviso, without which the claim fails for `X = ∅`), and
`X_reg` is open in `X` and dense in `X`. -/
theorem regularPoints_nonempty_open_dense {n : ℕ} {U X : Set (Fin n → ℂ)}
    (hX : IsSubvariety U X) :
    (X.Nonempty → (regularPoints X).Nonempty) ∧
      (∃ O : Set (Fin n → ℂ), IsOpen O ∧ regularPoints X = O ∩ X) ∧
      X ⊆ closure (regularPoints X) := by sorry

end LeblSCV.Varieties
