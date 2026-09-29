-- Prove2me | Theorems.Thm_MilnorDynamics_normal_disk_to_thrice_punctured_plane
-- name    : MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T11:06:50.795205+00:00
-- url     : https://prove2.me/theorems/892d47a3-020a-40c0-a979-085efb88a81a
-- title:
--   Corollary 3.3 — maps $\mathbb D\to\mathbb C\setminus\{0,1\}$ form a normal family
-- statement:
--   Let $\mathbb D$ be the open unit disk and let $\mathcal F$ be any family of holomorphic maps $f:\mathbb D\to\mathbb C\setminus\{0,1\}$. Then $\mathcal F$ is a **normal family** of maps into the noncompact surface $\mathbb C\setminus\{0,1\}$: every sequence $(f_n)$ in $\mathcal F$ has a subsequence $(f_{n_k})$ such that either
--
--   1. $f_{n_k}\to g$ locally uniformly on $\mathbb D$ for some continuous $g:\mathbb D\to\mathbb C\setminus\{0,1\}$, or
--   2. $(f_{n_k})$ diverges locally uniformly from $\mathbb C\setminus\{0,1\}$: for all compact $K\subseteq\mathbb D$ and $K'\subseteq\mathbb C\setminus\{0,1\}$, $f_{n_k}(K)\cap K'=\emptyset$ for all large $k$.
--
--   This is Milnor's Corollary 3.3 (every family of holomorphic maps between hyperbolic surfaces is normal) for the two hyperbolic surfaces $S=\mathbb D$ and $T=\mathbb C\setminus\{0,1\}$ (hyperbolic by Lemma 2.5). It is the local input to Montel's theorem.
--
--   **Formalization Note** Maps are functions $\mathbb C\to\mathbb C$ required to be holomorphic on $\mathbb D$ and to map $\mathbb D$ into $\mathbb C\setminus\{0,1\}$; normality is `MilnorDynamics.IsNormalFamilyInto` from the mission's definition file.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, p. 34, Corollary 3.3, special case S = unit disk, T = C \ {0,1}; normality as defined on p. 33

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem normal_disk_to_thrice_punctured_plane (𝓕 : Set (ℂ → ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      MapsTo f (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) :
    IsNormalFamilyInto (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) 𝓕 := by sorry

end MilnorDynamics
