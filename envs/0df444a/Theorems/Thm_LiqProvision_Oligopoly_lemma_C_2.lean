-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_lemma_C_2
-- name    : LiqProvision.Oligopoly.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:50.432866+00:00
-- url     : https://prove2.me/theorems/891d8f9e-06d7-4284-89be-87abee30c6dc
-- title:
--   Lemma C.2, p. 32 — integration by parts against a survival function
-- statement:
--   Let $f\ge0$ be integrable on $(0,\infty)$ and put $\bar F(x)=\int_x^\infty f(t)\,dt$. Let $g$ be integrable on every $[0,y]$ and put $G(x)=\int_0^x g(t)\,dt$. Suppose there is a nonnegative, nondecreasing $H$ on $[0,\infty)$ with $|G|\le H$ and $\int_0^\infty H(x)f(x)\,dx<\infty$. Then
--   $$\int_0^\infty G(x)f(x)\,dx=\lim_{y\to\infty}\int_0^y g(x)\bar F(x)\,dx .$$
--
--   It is the integration by parts used to rewrite the dealers' goal functionals.
--
--   **Formalization Note.** Generic statement. The page states the conclusion with a minus sign, $\int_0^\infty Gf=-\int_0^\infty g\bar F$, which is false (take $f(x)=e^{-x}$, $g\equiv1$, $G(x)=H(x)=x$: both sides of the corrected identity equal $1$). The proof on p. 32 derives the identity with a plus sign. The right side is stated as an improper integral, as the proof obtains it, because $g\bar F$ need not be absolutely integrable. Absolute continuity of $\bar F$ and $G$ follows from their integral forms and is not a separate hypothesis. "Borel" is subsumed by integrability.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 32, Lemma C.2

import Mathlib

namespace LiqProvision.Oligopoly
open Filter Topology in
theorem lemma_C_2 (f g H : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hfint : MeasureTheory.IntegrableOn f (Set.Ioi 0))
    (hgloc : ∀ y, 0 ≤ y → MeasureTheory.IntegrableOn g (Set.Icc 0 y))
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hHmono : MonotoneOn H (Set.Ici 0))
    (hGH : ∀ x, 0 ≤ x → |∫ t in (0 : ℝ)..x, g t| ≤ H x)
    (hHf : MeasureTheory.IntegrableOn (fun x => H x * f x) (Set.Ici 0)) :
    Tendsto (fun y => ∫ x in (0 : ℝ)..y, g x * ∫ t in Set.Ioi x, f t) atTop
      (𝓝 (∫ x in Set.Ioi 0, (∫ t in (0 : ℝ)..x, g t) * f x)) := by sorry
end LiqProvision.Oligopoly
