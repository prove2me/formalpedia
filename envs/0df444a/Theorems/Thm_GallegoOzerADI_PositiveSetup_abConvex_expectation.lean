-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_abConvex_expectation
-- name    : GallegoOzerADI.PositiveSetup.abConvex_expectation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:47:47.66112+00:00
-- url     : https://prove2.me/theorems/67cce4d1-29e5-4c54-af38-ad7f074851fa
-- title:
--   Lemma 1, Part 4 — $F(x) = E_{D,Y} f(x - D, Y) \in C(a,b)$
-- statement:
--   Let $a, b \ge 0$ and let $f : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}$ be such that $x \mapsto f(x, y)$ belongs to $C(a,b)$ for every fixed vector $y \in \mathbb{R}^n$. Let $D$ be a real random variable and $Y$ a random vector in $\mathbb{R}^n$, both defined on a probability space $(\Omega, \mathcal F, P)$, and assume that $f(x - D, Y)$ is integrable for every $x \in \mathbb{R}$. Then
--
--   $$
--   F(x) = \mathbb{E}_{D,Y}\, f(x - D, Y) \in C(a,b).
--   $$
--
--   Averaging over a random shift of the argument and a random parameter preserves $(a,b)$-convexity. This is the step that carries $K$-convexity of $J_{t+1}(\cdot, o_{t+1})$ through the expectation in the functional equation (9), where the shift is the demand and the parameter is the updated observed-demand vector.
--
--   **Formalization Note** The paper's integrability hypothesis is written $E_D|f(x - D, y)| < \infty$ for fixed $y$, while its conclusion integrates over $(D, Y)$ jointly. It is formalized as joint integrability of $\omega \mapsto f(x - D(\omega), Y(\omega))$ for every $x$, which is what the conclusion requires. Part 3 of the lemma is the special case in which $f$ does not depend on $y$.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1349, Lemma 1, Part 4 (proof p. 1358)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

theorem abConvex_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f : ℝ → (Fin n → ℝ) → ℝ) (hf : ∀ y, ABConvex a b (fun x => f x y))
    (D : Ω → ℝ) (Y : Ω → (Fin n → ℝ))
    (hint : ∀ x, Integrable (fun ω => f (x - D ω) (Y ω)) P) :
    ABConvex a b (fun x => ∫ ω, f (x - D ω) (Y ω) ∂P) := by sorry

end GallegoOzerADI.PositiveSetup
