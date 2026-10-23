-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_8
-- name    : MICPRep.Periodic.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:20.758027+00:00
-- url     : https://prove2.me/theorems/f03995c3-f13a-461f-92aa-9e1c77267725
-- title:
--   Lemma 6.8, p. 28 — an affine function separates a concave g from a convex f ≥ g on a convex set
-- statement:
--   Let $I \subseteq \mathbb R^d$ be convex and let $f, g : I \to \mathbb R$ be such that $f$ and $-g$ are convex and $g(z) \le f(z)$ for all $z \in I$. Then there are $v \in \mathbb R^d$ and $K \in \mathbb R$ with
--   $$g(z) \le v^{\mathsf T}z + K \le f(z) \qquad \forall z \in I.$$
--
--   The paper cites Rockafellar §31; it is used to turn bounded width functions into periodic directions in Lemma 6.13.
--
--   **Formalization Note** $f, g$ are total functions on $\mathbb R^d$ whose values off $I$ are irrelevant; convexity of $f$ and concavity of $g$ are Mathlib's `ConvexOn`/`ConcaveOn` on $I$. No closedness or nonemptiness of $I$ is assumed.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 28, Lemma 6.8

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.8, p. 28. -/
theorem lemma_6_8 {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (f g : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ I f) (hg : ConcaveOn ℝ I g)
    (hgf : ∀ z ∈ I, g z ≤ f z) :
    ∃ (v : Fin d → ℝ) (K : ℝ), ∀ z ∈ I, g z ≤ v ⬝ᵥ z + K ∧ v ⬝ᵥ z + K ≤ f z := by sorry

end MICPRep.Periodic
