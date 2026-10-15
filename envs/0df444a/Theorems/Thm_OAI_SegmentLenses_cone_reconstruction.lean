-- Prove2me | Theorems.Thm_OAI_SegmentLenses_cone_reconstruction
-- name    : OAI.SegmentLenses.cone_reconstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:11:46.825615+00:00
-- url     : https://prove2.me/theorems/19baf2f7-3db9-4db4-96ba-c57856bbd7ad
-- title:
--   Norm bound for averaged segment functionals placed in the cones above distinct gates
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$. A vertex $g$ is a *gate* of a finite set $H$ if $g\notin H$ and every $v<g$ lies in $H$. A *finite law* $\mu$ on a finite set $\Omega$ is a weight function with $\mu(\omega)\ge0$ for all $\omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$. For $f$ with values in $\mathbb{R}$ or in $J_V^{*}$ write $\mathbb{E}_\mu f=\sum_{\omega\in\Omega}\mu(\omega)\,f(\omega)$.
--
--   Let $H\subseteq V$ be finite (not necessarily ancestral), and let $G\subseteq V$ be a finite set all of whose elements are gates of $H$. Let $\mu$ be a finite law on a finite set $\Omega$, let $\varepsilon:\Omega\to\mathbb{R}$ satisfy $|\varepsilon(\omega)|\le1$, let $b:\Omega\times G\to\mathbb{R}$, and let $J_{g,\omega}\subseteq V$ ($g\in G$, $\omega\in\Omega$) be finite sets such that
--
--   - each $J_{g,\omega}$ is empty or a segment, and
--   - $g\le v$ for every $v\in J_{g,\omega}$.
--
--   Then
--   $$
--   \Big\|\sum_{g\in G}\ \sum_{\omega\in\Omega}\mu(\omega)\,\varepsilon(\omega)\,b(\omega,g)\,\sigma_{J_{g,\omega}}\Big\|_{J_V^{*}}\le\Big(\sum_{g\in G}\big(\mathbb{E}_\mu|b(\cdot,g)|\big)^2\Big)^{1/2}.
--   $$
--
--   Each piece $J_{g,\omega}$ lies in the cone of descendants of its gate $g$. The bound says that the dual norm sees, gate by gate, only the average absolute coefficient $\mathbb{E}_\mu|b(\cdot,g)|$, combined in $\ell_2$ across the gates; how the pieces vary with $\omega$ does not matter. In the finite midpoint tail bound it controls the tails of averaged replacement representations, which have exactly this form.
--
--   **Formalization Note** `b : Ω → G → ℝ` and `J : G → Ω → Finset V` are indexed by the elements of the finset `G`. The left-hand side is `∑ g, μ.expect (fun ω => (σ ω * b ω g) • segmentFunctional (J g ω))`, where `σ` is the sign function written $\varepsilon$ above. The right-hand side is `Real.sqrt` of a nonnegative number. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/HeadTests.lean#L154-L213

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

theorem OAI.SegmentLenses.cone_reconstruction {H : Finset V} (G : Finset V) (hG : ∀ g ∈ G, Gate H g)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (b : Ω → G → ℝ) (J : G → Ω → Finset V)
    (hJ : ∀ g ω, J g ω = ∅ ∨ SegmentSystem.isSegment (J g ω))
    (hcone : ∀ g ω v, v ∈ J g ω → g.val ≤ v) :
    ‖∑ g : G, μ.expect (fun ω => (σ ω * b ω g) • segmentFunctional (J g ω))‖ ≤
      Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) := by sorry
