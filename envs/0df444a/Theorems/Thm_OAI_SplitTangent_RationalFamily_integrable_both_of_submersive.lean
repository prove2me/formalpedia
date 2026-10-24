-- Prove2me | Theorems.Thm_OAI_SplitTangent_RationalFamily_integrable_both_of_submersive
-- name    : OAI.SplitTangent.RationalFamily.integrable_both_of_submersive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:37:59.137855+00:00
-- url     : https://prove2.me/theorems/5e6ab685-9ab8-4e2e-96a7-1879d9ff128c
-- title:
--   A family of rational curves whose two-point evaluation is submersive forces both summands of a tangent splitting to be integrable (OpenAI split tangent bundles, cf. Proposition 3.1)
-- statement:
--   **Notation** (published bundle `Def_SplitTangentIntegrability`). A `ComplexManifold` $X$ is a Hausdorff, second-countable space with a holomorphic atlas modeled on $\mathbb C^{d}$, $d$ = `X.dim`. A `ProjectiveEmbedding` $e$ of $X$ is an injective holomorphic immersion into some $\mathbb P^N(\mathbb C)$, given patchwise in affine coordinates. A `RationalCurve` $g$ in $X$ is a pair of holomorphic maps $g_0, g_\infty : \mathbb C \to X$ with $g_0(z) = g_\infty(1/z)$ for $z \ne 0$, i.e. a holomorphic map $\mathbb P^1 \to X$. $X$ is rationally connected with respect to $e$ (`RationallyConnected e`) when there is a nonempty dense set $U \subseteq X \times X$, the nonvanishing locus of bihomogeneous polynomials in the two image points, such that every pair in $U$ lies on one rational curve. A `TangentSplitting` $S$ is a holomorphic family of idempotent endomorphisms $P_x$ of the tangent spaces whose image and kernel have positive dimension everywhere. `S.first` and `S.second` are the image and kernel distributions, and a distribution is integrable (`Integrable`) when the Lie bracket of any two holomorphic vector fields with values in it, on any open set, again takes values in it.
--
--   **Families of rational curves** (definitions bundle `OAIQWST002` of this split). For complex manifolds $X$ and $T$, a `RationalFamily X T` is a holomorphic family $G$ of rational curves in $X$ parametrized by $T$: holomorphic maps $G_0, G_\infty : \mathbb C \times T \to X$ with $G_0(z, \tau) = G_\infty(1/z, \tau)$ for $z \ne 0$. Its two-point evaluation at $a, b \in \mathbb C$ (`twoPointEvaluation a b`) is $\tau \mapsto (G_0(a, \tau), G_0(b, \tau)) \in X \times X$.
--
--   **The statement.** Let $X$ be compact and connected with a projective embedding $e$, let $T$ be nonempty, let $G$ be a rational family in $X$ over $T$, and let $S$ be a tangent splitting of $X$. If for some $a, b \in \mathbb C$ the two-point evaluation $\tau \mapsto (G_0(a,\tau), G_0(b,\tau))$ has surjective differential at every $\tau \in T$, then both summands are integrable:
--   $$\texttt{Integrable}\ X\ S.\mathrm{first} \ \wedge\ \texttt{Integrable}\ X\ S.\mathrm{second}.$$
--
--   Lean: `OAI.SplitTangent.RationalFamily.integrable_both_of_submersive`, OpenAI's theorem of that name (in `lean/OAI/Geometry/SplitTangent/RationalFamilies.lean`).
-- source:
--   OpenAI, Integrability of split tangent bundles on rationally connected manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf, cf. Proposition 3.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/SplitTangent/RationalFamilies.lean (declaration OAI.SplitTangent.RationalFamily.integrable_both_of_submersive)

import Mathlib
import Definitions.Def_SplitTangentIntegrability
import Definitions.Def_OAIQWST002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff

open Filter Topology Set
open scoped ContDiff

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology

open Set Filter Topology

open Filter Topology

open Filter Topology

open Filter Topology Metric Set

open MvPowerSeries

open Filter Topology Set Metric

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

open Set Filter Topology
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

open Set Filter Topology
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

open Set Filter Topology
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff ENNReal

open Set Filter Topology
open scoped ContDiff ENNReal

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

namespace SplitTangent.RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

theorem integrable_both_of_submersive [CompactSpace X.Carrier]
    [ConnectedSpace X.Carrier] [Nonempty T.Carrier]
    (e : ProjectiveEmbedding X) (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ)) :
    Integrable X S.first ∧ Integrable X S.second := by
  sorry
end SplitTangent.RationalFamily

end

end OAI
end
