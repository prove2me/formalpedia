-- Prove2me | Theorems.Thm_OAI_SplitTangent_RationallyConnected_exists_submersive_familyAlternative
-- name    : OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:38:00.439132+00:00
-- url     : https://prove2.me/theorems/7886292a-08d7-45a0-8d3a-b1f1b00dceea
-- title:
--   A rationally connected projective manifold has a family of rational curves with submersive two-point evaluation (OpenAI split tangent bundles, cf. Lemma 4.1)
-- statement:
--   **Notation** (published bundle `Def_SplitTangentIntegrability`). A `ComplexManifold` $X$ is a Hausdorff, second-countable space with a holomorphic atlas modeled on $\mathbb C^{d}$, $d$ = `X.dim`. A `ProjectiveEmbedding` $e$ of $X$ is an injective holomorphic immersion into some $\mathbb P^N(\mathbb C)$, given patchwise in affine coordinates. A `RationalCurve` $g$ in $X$ is a pair of holomorphic maps $g_0, g_\infty : \mathbb C \to X$ with $g_0(z) = g_\infty(1/z)$ for $z \ne 0$, i.e. a holomorphic map $\mathbb P^1 \to X$. $X$ is rationally connected with respect to $e$ (`RationallyConnected e`) when there is a nonempty dense set $U \subseteq X \times X$, the nonvanishing locus of bihomogeneous polynomials in the two image points, such that every pair in $U$ lies on one rational curve. A `TangentSplitting` $S$ is a holomorphic family of idempotent endomorphisms $P_x$ of the tangent spaces whose image and kernel have positive dimension everywhere. `S.first` and `S.second` are the image and kernel distributions, and a distribution is integrable (`Integrable`) when the Lie bracket of any two holomorphic vector fields with values in it, on any open set, again takes values in it.
--
--   **Families of rational curves** (definitions bundle `OAIQWST002` of this split). For complex manifolds $X$ and $T$, a `RationalFamily X T` is a holomorphic family $G$ of rational curves in $X$ parametrized by $T$: holomorphic maps $G_0, G_\infty : \mathbb C \times T \to X$ with $G_0(z, \tau) = G_\infty(1/z, \tau)$ for $z \ne 0$. Its two-point evaluation at $a, b$ (`twoPointEvaluation a b`) is $\tau \mapsto (G_0(a, \tau), G_0(b, \tau))$.
--
--   **The statement.** Let $X$ be compact of positive dimension, with a projective embedding $e$, and rationally connected with respect to $e$. Then there are a nonempty complex manifold $T$ (in the same universe) and a rational family $G$ in $X$ over $T$ whose two-point evaluation at $0$ and $1$,
--   $$\tau \mapsto (G_0(0, \tau),\ G_0(1, \tau)) \in X \times X,$$
--   has surjective differential at every $\tau \in T$.
--
--   Lean: `OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative`, OpenAI's theorem of that name (in `lean/OAI/Geometry/SplitTangent/RationalVariation.lean`).
-- source:
--   OpenAI, Integrability of split tangent bundles on rationally connected manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf, cf. Lemma 4.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/SplitTangent/RationalVariation.lean (declaration OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative)

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
open Set Filter Topology IsManifold
open scoped ContDiff Manifold
universe u
namespace SplitTangent
open AnalyticZeroCover RationalParameters

theorem RationallyConnected.exists_submersive_familyAlternative {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (hdim : 0<X.dim) :
    ∃T : ComplexManifold.{u}, Nonempty T.Carrier ∧
      ∃G : RationalFamily X T, ∀τ, Function.Surjective
        (mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
          (G.twoPointEvaluation 0 1) τ) := by
  sorry

end SplitTangent

end

end OAI
end
