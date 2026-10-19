-- Prove2me | Theorems.Thm_MazurTransfer_finite_of_surjective_of_expanding_northcott_height
-- name    : MazurTransfer.finite_of_surjective_of_expanding_northcott_height
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T19:37:26.627992+00:00
-- url     : https://prove2.me/theorems/af512ab0-ff5f-4bee-b2cf-a8057f488ee9
-- title:
--   A surjective map with an expanding Northcott height has finite domain
-- statement:
--   Let $h:X\to\mathbb R$ have finite sublevel sets and let $f:X\to X$ be surjective. If there are real constants $a>1$ and $C$ such that $a h(x)-C\le h(f(x))$ for every $x$, then $X$ is finite. No group structure or finite-generation hypothesis is required.
-- source:
--   Original finite-sublevel inverse-map argument by Vas and contributors, MazurTheorem project, October 16, 2026. Apache-2.0.

import Mathlib.Order.Northcott
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
universe u

theorem MazurTransfer.finite_of_surjective_of_expanding_northcott_height {X : Type u} (h : X → ℝ) (f : X → X) [Northcott h]
    (a C : ℝ) (ha : 1 < a) (hg : ∀ x, a * h x - C ≤ h (f x))
    (hf : Function.Surjective f) : Finite X := by sorry
