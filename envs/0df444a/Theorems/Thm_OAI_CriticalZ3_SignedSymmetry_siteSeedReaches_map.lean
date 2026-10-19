-- Prove2me | Theorems.Thm_OAI_CriticalZ3_SignedSymmetry_siteSeedReaches_map
-- name    : OAI.CriticalZ3.SignedSymmetry.siteSeedReaches_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:50:02.346322+00:00
-- url     : https://prove2.me/theorems/ca34aeac-1307-4b79-929b-8cc1eb9adca6
-- title:
--   Site seed events are equivariant under signed symmetries
-- statement:
--   Let $S$ be a signed symmetry of $\mathbb Z^3$ (a coordinate permutation with sign changes and a translation). For a site configuration $\omega$, cube radii $m\le n$ and a target set $T$,
--   $$
--   \omega\circ S\in\mathrm{SeedReach}(c,m,n,S^{-1}T)\iff\omega\in\mathrm{SeedReach}(S(c),m,n,T),
--   $$
--   where the seed event says that some open vertex of $\Lambda_m(\cdot)$ is joined to the target by open sites within $\Lambda_n(\cdot)$.
--
--   Since the site law is invariant under these symmetries, all quarter-face crossings have the same probability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean#L96-L110

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3 OAI.CriticalZ3.SignedSymmetry
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Classical

theorem OAI.CriticalZ3.SignedSymmetry.siteSeedReaches_map (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ siteSeedReaches (S.vertex c) m n T := by sorry
