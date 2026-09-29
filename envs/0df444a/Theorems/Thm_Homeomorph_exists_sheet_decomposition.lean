-- Prove2me | Theorems.Thm_Homeomorph_exists_sheet_decomposition
-- name    : Homeomorph.exists_sheet_decomposition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/70378820-55e7-5116-8c22-ac1ddc429221
-- title:
--   Sheets of a trivialised map over a smaller open set
-- statement:
--   Let $E$, $X$ and $I$ be topological spaces with $I$ discrete, let $f : E \to X$ be a function, let $U \subseteq X$ and let $\Omega \subseteq E$ be open. Assume given a homeomorphism $H : \Omega \xrightarrow{\ \sim\ } U \times I$ whose first component computes $f$, i.e. for every $x \in \Omega$ the point of $X$ underlying $(H x)_1 \in U$ equals $f(x)$, and let $V \subseteq X$ be open with $V \subseteq U$; assume $\Omega$ is nonempty. Then there exists a family $\zeta : I \to \mathrm{OpenPartialHomeomorph}\,E\,X$ of partial homeomorphisms with open source and target such that: every $\zeta i$ has target exactly $V$; for each $i$ and each $e$ in the source of $\zeta i$ one has $e \in \Omega$ and $\zeta i\,e = f(e)$; for each $i$ and each $z \in V$ the point $(\zeta i)^{-1}z$ lies in $\Omega$ and satisfies $f((\zeta i)^{-1}z) = z$; the sources of $\zeta i$ and $\zeta j$ are disjoint for $i \neq j$; and every $e \in \Omega$ with $f(e) \in V$ lies in the source of $\zeta i$ for some $i$.
--
--   This is the standard decomposition of an evenly covered piece of a map into sheets: over a smaller open set $V$ inside the trivialising set $U$, the trivialised part $\Omega$ of the total space splits into pairwise disjoint open pieces, each mapped homeomorphically onto $V$ by $f$, with local sections of $f$ given by the inverses. It is used in the construction of dissection data for algebraic curves, via [`AlgebraicCurve.exists_dissectionScaleData`](thm.html#AlgebraicCurve.exists_dissectionScaleData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Homeomorph_exists_sheet_decomposition.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Homeomorph.exists_sheet_decomposition {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] [DiscreteTopology I] {f : E → X} {U : Set X}
    {Ω : Set E} (hpre : IsOpen Ω) (H : Ω ≃ₜ U × I) (hH : ∀ x, ((H x).1 : X) = f x)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) [Nonempty Ω] :
    ∃ ζ : I → OpenPartialHomeomorph E X,
      (∀ i, (ζ i).target = V) ∧
      (∀ i, ∀ e ∈ (ζ i).source, e ∈ Ω ∧ ζ i e = f e) ∧
      (∀ i, ∀ z ∈ V, (ζ i).symm z ∈ Ω ∧ f ((ζ i).symm z) = z) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ e : E, e ∈ Ω → f e ∈ V → ∃ i, e ∈ (ζ i).source) := by sorry
