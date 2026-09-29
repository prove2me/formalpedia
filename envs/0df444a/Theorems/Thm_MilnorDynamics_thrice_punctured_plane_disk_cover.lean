-- Prove2me | Theorems.Thm_MilnorDynamics_thrice_punctured_plane_disk_cover
-- name    : MilnorDynamics.thrice_punctured_plane_disk_cover
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T10:43:17.127987+00:00
-- url     : https://prove2.me/theorems/9e9af915-3edd-47b0-8f23-44d7784f2f1f
-- title:
--   Lemma 2.5 — $\mathbb C\setminus\{0,1\}$ is covered holomorphically by the unit disk
-- statement:
--   Let $\mathbb D=\{z\in\mathbb C: |z|<1\}$ be the open unit disk and let $\mathbb C\setminus\{0,1\}=\hat{\mathbb C}\setminus\{0,1,\infty\}$ be the thrice-punctured sphere. There is a holomorphic map
--   $$
--   p:\mathbb D\to\mathbb C\setminus\{0,1\}
--   $$
--   which is surjective and a covering map. Since $\mathbb D$ is simply connected, $p$ is a universal covering, so the thrice-punctured sphere is a hyperbolic Riemann surface.
--
--   This is the case of Milnor's Lemma 2.5 used in the proof of Montel's theorem: via Corollary 3.3 it makes every family of holomorphic maps into $\mathbb C\setminus\{0,1\}$ normal.
--
--   **Formalization Note** The covering map is recorded as a function $p:\mathbb C\to\mathbb C$, holomorphic on $\mathbb D$, mapping $\mathbb D$ into $\mathbb C\setminus\{0,1\}$, whose restriction $\mathbb D\to\mathbb C\setminus\{0,1\}$ (with subspace topologies) is surjective and a covering map in Mathlib's sense (`IsCoveringMap`). Milnor states the lemma for the sphere minus any three or more points; this item is the special case $\{0,1,\infty\}$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §2, p. 17, Lemma 2.5 (The Triply Punctured Sphere), special case of the sphere minus {0, 1, ∞}

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem thrice_punctured_plane_disk_cover :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) ∧
      ∃ hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        Function.Surjective hp.restrict ∧ IsCoveringMap hp.restrict := by sorry

end MilnorDynamics
