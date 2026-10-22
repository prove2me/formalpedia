-- Prove2me | Theorems.Thm_GeomDL_Blueprint_sidenote_p20_eps_isometry_comp
-- name    : GeomDL.Blueprint.sidenote_p20_eps_isometry_comp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:21.877508+00:00
-- url     : https://prove2.me/theorems/036a7ebb-0a47-42d7-a228-6b511c5e4c19
-- title:
--   §3.3, side-note p. 20 — the composition of two ε-isometries is a 2ε-isometry, violating closure
-- statement:
--   Call a self-map $\tau$ of a metric space $(X, d)$ an **$\varepsilon$-isometry** if its metric distortion is at most $\varepsilon$, i.e. $|d(\tau u, \tau v) - d(u, v)| \le \varepsilon$ for all $u, v \in X$.
--
--   1. On every metric space, if $\tau_1$ is an $\varepsilon_1$-isometry and $\tau_2$ is an $\varepsilon_2$-isometry, then $\tau_1 \circ \tau_2$ is an $(\varepsilon_1 + \varepsilon_2)$-isometry; in particular
--   $$\tau_1, \tau_2 \text{ are } \varepsilon\text{-isometries} \implies \tau_1 \circ \tau_2 \text{ is a } 2\varepsilon\text{-isometry}.$$
--   2. The $\varepsilon$-isometries are not closed under composition: for every $\varepsilon > 0$ there is a continuous bijection $\tau : \mathbb R \to \mathbb R$ which is an $\varepsilon$-isometry while $\tau \circ \tau$ is not.
--
--   This is why "small deformations" do not form a group, and why the book replaces exact invariance to deformations by deformation stability.
--
--   **Formalization Note** The book's side-note gives no space; part 2 makes "violating the closure property" concrete on the real line, with a continuous bijection so that the counterexample is a genuine deformation. Part 1 holds on pseudometric spaces.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.3, side-note p. 20; metric distortion dis(η), §4.4, p. 51

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

/-- Bronstein et al., §3.3, side-note p. 20: "E.g., the composition of two ε-isometries is a
2ε-isometry, violating the closure property." (An ε-isometry has metric distortion at most ε,
§4.4, p. 51.)
1. On any (pseudo)metric space, the composition of an `ε₁`-isometry and an `ε₂`-isometry is an
   `(ε₁ + ε₂)`-isometry; in particular two `ε`-isometries compose to a `2ε`-isometry.
2. Closure fails: for every `ε > 0` there is a continuous bijection `τ : ℝ → ℝ` that is an
   `ε`-isometry while `τ ∘ τ` is not. -/
theorem sidenote_p20_eps_isometry_comp :
    (∀ {X : Type} [PseudoMetricSpace X] (ε₁ ε₂ : ℝ) (τ₁ τ₂ : X → X),
      IsEpsIsometry ε₁ τ₁ → IsEpsIsometry ε₂ τ₂ → IsEpsIsometry (ε₁ + ε₂) (τ₁ ∘ τ₂)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ τ : ℝ → ℝ, Continuous τ ∧ Function.Bijective τ ∧
      IsEpsIsometry ε τ ∧ ¬ IsEpsIsometry ε (τ ∘ τ)) := by sorry

end GeomDL.Blueprint
