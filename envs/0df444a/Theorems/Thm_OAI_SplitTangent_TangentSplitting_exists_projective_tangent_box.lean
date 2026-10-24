-- Prove2me | Theorems.Thm_OAI_SplitTangent_TangentSplitting_exists_projective_tangent_box
-- name    : OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:38:08.078406+00:00
-- url     : https://prove2.me/theorems/07dcd224-00cf-441d-afe3-6e3963ddc24f
-- title:
--   Every rational curve in a projective manifold with a split tangent bundle has a tangent box (OpenAI split tangent bundles, Proposition 2.1)
-- statement:
--   **Notation** (published bundle `Def_SplitTangentIntegrability`). A `ComplexManifold` $X$ is a Hausdorff, second-countable space with a holomorphic atlas modeled on $\mathbb C^{d}$, $d$ = `X.dim`. A `ProjectiveEmbedding` $e$ of $X$ is an injective holomorphic immersion into some $\mathbb P^N(\mathbb C)$, given patchwise in affine coordinates. A `RationalCurve` $g$ in $X$ is a pair of holomorphic maps $g_0, g_\infty : \mathbb C \to X$ with $g_0(z) = g_\infty(1/z)$ for $z \ne 0$, i.e. a holomorphic map $\mathbb P^1 \to X$. $X$ is rationally connected with respect to $e$ (`RationallyConnected e`) when there is a nonempty dense set $U \subseteq X \times X$, the nonvanishing locus of bihomogeneous polynomials in the two image points, such that every pair in $U$ lies on one rational curve. A `TangentSplitting` $S$ is a holomorphic family of idempotent endomorphisms $P_x$ of the tangent spaces whose image and kernel have positive dimension everywhere. `S.first` and `S.second` are the image and kernel distributions, and a distribution is integrable (`Integrable`) when the Lie bracket of any two holomorphic vector fields with values in it, on any open set, again takes values in it.
--
--   **Tangent boxes** (definitions bundle `OAIQWST002` of this split). For a tangent splitting $S$ of $X$ and a rational curve $g$, a `TangentBox S g` is a holomorphic map from $\mathbb P^1 \times \mathbb P^1$ to $X$, given on the four affine charts $\mathbb C \times \mathbb C$ (`chart a b`, compatible on overlaps through $z \mapsto 1/z$ in each coordinate, `ReciprocalCharts`), such that:
--   - on the diagonal it is $g$: `chart false false (z, z)` $= g_0(z)$ and `chart true true (z, z)` $= g_\infty(z)$;
--   - at every point, its derivative in the first coordinate direction lies in `S.first` and in the second coordinate direction lies in `S.second`.
--
--   **The statement.** Let $X$ be compact with a projective embedding $e$, let $S$ be a tangent splitting of $X$, and let $g$ be a rational curve in $X$. Then $g$ has a tangent box: `TangentBox S g` is nonempty.
--
--   This is the Lean form of the paper's Proposition 2.1 (tangent box), for curves in a projective manifold.
--
--   Lean: `OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box`, OpenAI's theorem of that name (in `lean/OAI/Geometry/SplitTangent/FormalBoxes.lean`).
-- source:
--   OpenAI, Integrability of split tangent bundles on rationally connected manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf, Proposition 2.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/SplitTangent/FormalBoxes.lean (declaration OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box)

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
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
universe u
open Set Filter Topology

open Filter Topology

open Filter Topology

open Filter Topology Metric Set

open MvPowerSeries

open Filter Topology Set Metric

namespace SplitTangent
namespace TangentSplitting
open ReciprocalCharts
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

theorem exists_projective_tangent_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) : Nonempty (TangentBox S g) := by
  sorry

end TangentSplitting
end SplitTangent

end

end OAI
end
