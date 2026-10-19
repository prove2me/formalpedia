-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_scalarNestedSourceDegreeGlobalization_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_scalarNestedSourceDegreeGlobalization_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T09:35:00.385097+00:00
-- url     : https://prove2.me/theorems/12c4b5a9-f41a-4011-be8d-c0145b38005e
-- title:
--   Exponents exist making the scalar nested source give degree globalization
-- statement:
--   For all $s, \mathrm{initial}, \mathrm{extra}, \mathrm{baseFloor} \in \mathbb{N}$ there is $\mathrm{exponent} \in \mathbb{N}$ with $3 \le \mathrm{exponent}$ and there is $\mathrm{baseMin} \in \mathbb{N}$ with $\mathrm{baseFloor} \le \mathrm{baseMin}$ and $1 \le \mathrm{baseMin}$ such that for every $\mathrm{basePower} \ge \mathrm{baseMin}$ there is $\mathrm{earlyExponent} \ge 2$ such that for every $\mathrm{latePower} \in \mathbb{N}$ there is $\mathrm{sizeExponent} \ge 2$ with `ScalarNestedSourceDegreeGlobalization s initial exponent basePower earlyExponent latePower sizeExponent`. (The argument $\mathrm{extra}$ does not occur in the conclusion.)
--
--   `ScalarNestedSourceDegreeGlobalization s initial exponent basePower earlyExponent latePower sizeExponent` is the proposition: for all $n_X \in \mathbb{N}$ and reals $p \ge 2$ with $n_X \le p$, and every allocated external candidate sampler `A₀` with an empty layer index set ($\mathrm{Fin}\ 0$), over the group $\mathrm{Fin}$ (`scalarNativeDimension s`) ($= (s+1)(s+3)$), with box sizes $N : \mathrm{Fin}\ n_X \to \mathbb{N}$, trim $\tau$, narrow width $\xi_0$, all strides $1$ and residue cell set $\{0\}$ (`AllocatedExternalCandidateSampler`, a proposition bundling positivity and nonemptiness conditions), if $\xi_0 \le 1$, $\tau = $ `unconditionedSpatialTrimFraction nX (exp (-p))` $= e^{-p}/(32(n_X+1))$, $\exp((p+2)^{\mathrm{earlyExponent}}) \le$ `S₀.value` $\le \exp((p+2)^{\mathrm{latePower}})$ for its `LayerSamplerScale` $S_0$, $\exp((p+2)^{\mathrm{sizeExponent}}) \le N_i$ for all $i$, and, with $B_{\mathrm{struct}} = (p+2)^{\mathrm{basePower}}$ and $\mathrm{finalSeed} = $ `candidateNestedForwardSeed exponent degreeSourceCountConstants (s + 1) (2 * s) Bstruct`, $e^{\mathrm{finalSeed}} \le$ `S₀.value`, then for every $\mathrm{weight} : \mathbb{Z}^{n_X} \to \mathbb{C}$, `A₀.DegreeGlobalizationAt weight s initial Bstruct (candidateDegreeReturnBudget s finalSeed)` holds (`candidateDegreeReturnBudget s y` $= 3^s(y+1) - 1$).
--
--   `A.DegreeGlobalizationAt weight degree netExponent p outputCost` is the proposition: for all rational filtered nilmanifolds $D$ and $F_{\mathrm{mark}}$ of step `degree` and every Lie algebra map $\varphi$ mapping each filtration layer of $D$ onto the corresponding layer of $F_{\mathrm{mark}}$, if both geometries have complexity at most $p$ and the coefficients of $\varphi$ have rational log height at most $p$, then for every marked polynomial orbit and every family of observables (indexed by $\mathbb{Z}^{n_X}$) that are $\ell$-Lipschitz with $\ell \le e^p$, real with values in $[0,1]$, and for every $\eta \in (0,1]$ covered on the box to within $\eta$ by at most $\exp((p + \log(1/\eta) + \mathrm{netExponent})^{\mathrm{netExponent}})$ of them, if $\|\mathrm{weight}\| \le e^p$ then every `AllocatedExternalCandidateProblem` for these data with parameters $p, e^{-p}, e^{-p}$ has a `Conclusion` with parameters $\mathrm{outputCost}, e^{-\mathrm{outputCost}}, e^{-\mathrm{outputCost}}$. `candidateNestedForwardSeed` is the value of OpenAI's natural-coefficient polynomial `candidateNestedForwardSeedPolynomial`, and `degreeSourceCountConstants` is $r \mapsto$ `fullChartStageCountConstant (r + 1) 254`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_scalarNestedSourceDegreeGlobalization_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_scalarNestedSourceDegreeGlobalization` (in `lean/OAI/Combinatorics/Progressions/Polynomial/ScalarNestedSourceDegreeGlobalization.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B296` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/ScalarNestedSourceDegreeGlobalization.lean (declaration OAI.Erdos3.VectorPolynomial.exists_scalarNestedSourceDegreeGlobalization)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B296

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_scalarNestedSourceDegreeGlobalization_s2
    (s initial extra baseFloor : ℕ) :
    ∃ exponent : ℕ, 3 ≤ exponent ∧
      ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
        ∀ basePower : ℕ, baseMin ≤ basePower →
        ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
          ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
            ScalarNestedSourceDegreeGlobalization s initial exponent basePower
              earlyExponent latePower sizeExponent := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
