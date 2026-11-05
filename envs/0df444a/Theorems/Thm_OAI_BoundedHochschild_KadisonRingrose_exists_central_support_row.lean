-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_central_support_row
-- name    : OAI.BoundedHochschild.KadisonRingrose.exists_central_support_row
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:43:24.389071+00:00
-- url     : https://prove2.me/theorems/b1548e3d-838e-4963-b1e0-0371bb5a3a2a
-- title:
--   A row of partial isometries reaching the central support of a projection
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(x)\to e^{-1}(b)(x)$ for every $x\in X$. A cochain of degree $k$ is a bounded complex $k$-linear map $M^k\to M$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$. A partial isometry (`PartialIso`) is an element $v$ with $vv^*v=v$; its initial and final projections are $v^*v$ and $vv^*$. Let $p$ be a projection with central support $z$ (`IsCentralSupport p z`: $z$ is a central projection, $p\le z$, and any central projection $c$ with $cp=0$ has $cz=0$). Then there is a set $S$ of partial isometries with $vv^*\le p$ and $v^*v\le z$ for $v\in S$, with pairwise orthogonal initial projections, such that
--
--   $$\sum_{v\in s}v^*v\longrightarrow z\qquad(s\subset S\text{ finite})$$
--
--   in the predual sense.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.exists_central_support_row`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/CentralSupportRows.lean#L23

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_central_support_row (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p z : M} (hp : IsStarProjection p) (hz : IsCentralSupport p z) :
    ∃ S : Set (PartialIso M),
      (∀ v ∈ S, v.final ≤ p ∧ v.initial ≤ z) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w → v.initial * w.initial = 0) ∧
      PredualTendsto e (fun s : Finset S => ∑ v ∈ s, v.val.initial) atTop z := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
