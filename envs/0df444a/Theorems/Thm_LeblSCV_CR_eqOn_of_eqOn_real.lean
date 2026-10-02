-- Prove2me | Theorems.Thm_LeblSCV_CR_eqOn_of_eqOn_real
-- name    : LeblSCV.CR.eqOn_of_eqOn_real
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:26:36.487975+00:00
-- url     : https://prove2.me/theorems/646a66fa-c5b3-4f52-991a-e30cae20d694
-- title:
--   Lemma 3.1.2 — holomorphic functions agreeing on $V \cap \mathbb{R}^n$ agree on $V$
-- statement:
--   Let $\mathbb{R}^n \subset \mathbb{C}^n$ be the natural inclusion and let $V \subset \mathbb{C}^n$ be a domain (a nonempty connected open set) with $V \cap \mathbb{R}^n \neq \emptyset$. If $f, g : V \to \mathbb{C}$ are holomorphic and $f = g$ on $V \cap \mathbb{R}^n$, then
--   $$f = g \quad \text{on } V.$$
--   The real slice $\mathbb{R}^n$ has empty interior in $\mathbb{C}^n$, so this is a uniqueness theorem beyond the ordinary identity theorem; it is what makes complexification (Proposition 3.1.3) unique.
--
--   **Formalization Note.** Holomorphic on the open set $V$ is `DifferentiableOn ℂ` (equivalent to the book's Definition 1.1.2 on open sets by Proposition 1.1.3 and Theorem 1.2.1). A domain is `IsOpen V ∧ IsConnected V`; $\mathbb{R}^n$ is `Set.range realEmbed`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 104, Lemma 3.1.2

import Mathlib
import Definitions.Def_LeblSCV_CR_realEmbed

namespace LeblSCV.CR

/-- Lemma 3.1.2 (Lebl, p. 104): let `ℝⁿ ⊂ ℂⁿ` be the natural inclusion and `V ⊂ ℂⁿ` a domain with
`V ∩ ℝⁿ ≠ ∅`. If `f, g` are holomorphic on `V` and `f = g` on `V ∩ ℝⁿ`, then `f = g` on `V`. -/
theorem eqOn_of_eqOn_real {n : ℕ} (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hVc : IsConnected V)
    (hVR : (V ∩ Set.range (realEmbed (n := n))).Nonempty) (f g : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (hfg : ∀ z ∈ V ∩ Set.range (realEmbed (n := n)), f z = g z) :
    Set.EqOn f g V := by sorry

end LeblSCV.CR
