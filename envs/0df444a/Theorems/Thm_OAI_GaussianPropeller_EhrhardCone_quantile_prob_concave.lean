-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_EhrhardCone_quantile_prob_concave
-- name    : OAI.GaussianPropeller.EhrhardCone.quantile_prob_concave
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:18:44.523995+00:00
-- url     : https://prove2.me/theorems/51087ea9-f2e2-47e3-86e0-f81291518eb0
-- title:
--   Ehrhard-type concavity: the Gaussian quantile of the probability of a translated polyhedral cone is concave
-- statement:
--   Let $\iota$ and $\kappa$ be finite types (`Fintype`), $\kappa$ nonempty (`Nonempty κ`), and let $E = $ `EuclideanSpace ℝ ι` with inner product $\langle\cdot,\cdot\rangle$ and standard Gaussian measure $\gamma$ (Mathlib's `stdGaussian E`). Let $v : \kappa \to E$ be a family of vectors and $e \in E$ a vector with $\langle v_i, e\rangle > 0$ for every $i$.
--
--   Definitions used:
--   - The cone of $v$ is $C = \{y \in E : \langle v_i, y\rangle \ge 0 \text{ for all } i\}$ (`cone v`), and for $x \in E$, `shifted v x` is $\{y : x + y \in C\}$.
--   - `prob v x` is $\gamma(\{y : x + y \in C\})$, as a real number (`(stdGaussian E).real`).
--   - $\varphi(x) = (2\pi)^{-1/2} e^{-x^2/2}$ (`Quantile.φ`) and $\Phi(x) = \int_{(-\infty, x]} \varphi$ (`Quantile.Φ`). $\Phi$ is an order isomorphism from $\mathbb R$ onto $(0, 1)$ (`Quantile.cdfIso`), and the quantile function $q$ (`Quantile.q`) is its inverse on $(0,1)$, with $q(p) = 0$ for $p \notin (0,1)$.
--
--   Then the function $x \mapsto q(\mathrm{prob}\ v\ x)$ is concave on all of $E$ (`ConcaveOn ℝ univ`).
--
--   Lean: `OAI.GaussianPropeller.EhrhardCone.quantile_prob_concave`, OpenAI's lemma of that name (in `lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean`). `cone`, `shifted`, `prob`, `φ`, `Φ`, `cdfIso` and `q` come from the definitions bundle `OAIQWGP000` of this split.
-- source:
--   Ehrhard-type concavity of the Gaussian quantile (A. Ehrhard, Symétrisation dans l'espace de Gauss, Mathematica Scandinavica 53 (1983), 281–301, for convex sets). Proof: OpenAI, The Gaussian propeller bound in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 096; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean (declaration OAI.GaussianPropeller.EhrhardCone.quantile_prob_concave)

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uι uκ

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι

lemma quantile_prob_concave (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) :
    ConcaveOn ℝ univ (fun x => q (prob v x)) := by
  sorry

end GaussianPropeller.EhrhardCone

end OAI
end
