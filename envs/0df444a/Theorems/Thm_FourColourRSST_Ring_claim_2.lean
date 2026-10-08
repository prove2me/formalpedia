-- Prove2me | Theorems.Thm_FourColourRSST_Ring_claim_2
-- name    : FourColourRSST.Ring.claim_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:01.095422+00:00
-- url     : https://prove2.me/theorems/45a8ec88-8bb4-4944-a3d4-857307bfdc3d
-- title:
--   Proof of (6.4), claim (2), p. 26 — if 𝒜₁₃ ⊆ 𝒞 then 𝒞 includes one of 𝒜₂₃, 𝒜₃₅
-- statement:
--   Let $R$ be a circuit of length 5 with edges $e_1, \dots, e_5$ in order, and for $i \neq j$ let $\mathcal A_{ij}$ be the equivalence class of the edge-colouring with $\kappa(e_i) = 1$, $\kappa(e_j) = -1$ and $\kappa = 0$ on the other edges. Let $\mathcal C$ be a consistent set of edge-colourings of $R$. If $\mathcal A_{13} \subseteq \mathcal C$, then
--   $$\mathcal A_{23} \subseteq \mathcal C \quad\text{or}\quad \mathcal A_{35} \subseteq \mathcal C.$$
--
--   This is the second of the two claims in the proof of Birkhoff's lemma (6.4) for rings of length 5.
--
--   **Formalization Note.** Indices are 0-based in Lean: $\mathcal A_{13}$ = `A 0 2`, $\mathcal A_{23}$ = `A 1 2`, $\mathcal A_{35}$ = `A 2 4`. "Includes" is set inclusion.
-- source:
--   Robertson, Sanders, Seymour and Thomas, The Four-Colour Theorem, J. Combin. Theory Ser. B 70 (1997), author's manuscript (rev. 16 January 1997), p. 26, proof of (6.4), claim (2)

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting

namespace FourColourRSST.Ring

theorem claim_2 (C : Set (EdgeColouring 5)) (hC : Consistent C) (h13 : A 0 2 ⊆ C) :
    A 1 2 ⊆ C ∨ A 2 4 ⊆ C := by sorry

end FourColourRSST.Ring
