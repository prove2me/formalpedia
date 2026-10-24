-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_exists_lipschitzWith_smul_of_locallyLipschitz_408915f
-- name    : FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:17:56.005133+00:00
-- url     : https://prove2.me/theorems/50b6cb14-d4b2-403f-89a9-d010a2004e30
-- title:
--   Global Lipschitzness of a Compactly Supported Cutoff Product
-- statement:
--   This is the cutoff localization statement labeled S5d.
--
--   Let $V$ be a finite-dimensional real normed space, $V'$ a real normed space, and let $\gamma:V\to\mathbb R$ be Lipschitz with a nonnegative Lipschitz constant and compact support. Let $f:V\to V'$ be locally Lipschitz. Then there exist $K\in\mathbb R_{\ge0}$ and $B\in\mathbb R$ such that:
--
--   1. the map $x\mapsto\gamma(x)\,f(x)$ is globally Lipschitz with constant $K$;
--   2. for every $x\in V$,
--   $$\|\gamma(x)f(x)\|\le B.$$
--
--   Scalar multiplication is the given action of $\mathbb R$ on $V'$. The theorem is a compact-localization tool and does not assert a particular formula for either bound.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/LipschitzBall.lean#L53-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.LipschitzBall`, declaration `FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz

noncomputable section
open scoped NNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Diffusion
section Cutoff
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

theorem FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz_408915f {γ : V → ℝ} {Kγ : ℝ≥0}
    (hγ : LipschitzWith Kγ γ) (hγs : HasCompactSupport γ) {f : V → V'}
    (hf : LocallyLipschitz f) :
    (∃ K : ℝ≥0, LipschitzWith K fun x => γ x • f x) ∧ ∃ B : ℝ, ∀ x, ‖γ x • f x‖ ≤ B := by sorry
