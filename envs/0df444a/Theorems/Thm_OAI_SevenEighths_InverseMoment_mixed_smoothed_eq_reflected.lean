-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_mixed_smoothed_eq_reflected
-- name    : OAI.SevenEighths.InverseMoment.mixed_smoothed_eq_reflected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:57.147576+00:00
-- url     : https://prove2.me/theorems/269d6f5b-8cc1-443d-97e2-953406af77d1
-- title:
--   The mixed smoothed value equals its reflected form
-- statement:
--   Let $p:\iota\to\mathcal O$ ($\iota$ finite) be nonzero Eisenstein integers generating maximal, pairwise coprime ideals avoiding $\lambda_0=$`goodLambda` with residue characteristic $\ne2$, $D$ a `ControlledStratumArithmetic p N a0 c0 mode` with $9c_0\mid N$, $\lambda_0^2\mid\prod p_i-1$, the base condition on $a_0$ or $c_0$, $c_0\ne0$, `s` a `FixedCuspShape`, exponents $j_i<6$, $S\subseteq\iota$, $W$ smooth with support in $[lo,hi]$ ($lo>0$) and $X>0$. Then `mixedSmoothedValue D … s … j S W X` $=$ `mixedReflectedValue D s … j S W X`.
--
--   Lean: `OAI.SevenEighths.InverseMoment.mixed_smoothed_eq_reflected` in `lean/OAI/NumberTheory/DirichletL/Descent/ReflectedDual.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B024

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota CompletedDyadic
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseMoment.dualQuotientFintype
theorem mixed_smoothed_eq_reflected (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X =
      mixedReflectedValue D s hp hc0 hg j S W X := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
