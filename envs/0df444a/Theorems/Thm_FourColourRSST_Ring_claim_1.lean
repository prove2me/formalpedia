-- Prove2me | Theorems.Thm_FourColourRSST_Ring_claim_1
-- name    : FourColourRSST.Ring.claim_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:55.546286+00:00
-- url     : https://prove2.me/theorems/492f0f39-dc50-4fab-82de-a8b5d7122ae3
-- title:
--   Proof of (6.4), claim (1), p. 26 — if 𝒜₁₂ ⊆ 𝒞 then 𝒞 includes one of 𝒜₁₃, 𝒜₁₅ and one of 𝒜₂₃, 𝒜₂₅
-- statement:
--   Let $R$ be a circuit of length 5 with edges $e_1, \dots, e_5$ in order, and for $i \neq j$ let $\mathcal A_{ij}$ be the equivalence class of the edge-colouring with $\kappa(e_i) = 1$, $\kappa(e_j) = -1$ and $\kappa = 0$ on the other edges. Let $\mathcal C$ be a consistent set of edge-colourings of $R$. If $\mathcal A_{12} \subseteq \mathcal C$, then
--   $$\bigl(\mathcal A_{13} \subseteq \mathcal C \ \text{ or }\ \mathcal A_{15} \subseteq \mathcal C\bigr) \quad\text{and}\quad \bigl(\mathcal A_{23} \subseteq \mathcal C \ \text{ or }\ \mathcal A_{25} \subseteq \mathcal C\bigr).$$
--
--   This is the first of the two claims in the proof of Birkhoff's lemma (6.4) for rings of length 5.
--
--   **Formalization Note.** Indices are 0-based in Lean: $\mathcal A_{12}$ = `A 0 1`, $\mathcal A_{13}$ = `A 0 2`, $\mathcal A_{15}$ = `A 0 4`, $\mathcal A_{23}$ = `A 1 2`, $\mathcal A_{25}$ = `A 1 4`. "Includes" is set inclusion.
-- source:
--   Robertson, Sanders, Seymour and Thomas, The Four-Colour Theorem, J. Combin. Theory Ser. B 70 (1997), author's manuscript (rev. 16 January 1997), p. 26, proof of (6.4), claim (1)

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting

namespace FourColourRSST.Ring

theorem claim_1 (C : Set (EdgeColouring 5)) (hC : Consistent C) (h12 : A 0 1 ⊆ C) :
    (A 0 2 ⊆ C ∨ A 0 4 ⊆ C) ∧ (A 1 2 ⊆ C ∨ A 1 4 ⊆ C) := by sorry

end FourColourRSST.Ring
