-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_manuscriptRelativePatchPower_s2
-- name    : OAI.Erdos3.exists_manuscriptRelativePatchPower_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:06.937649+00:00
-- url     : https://prove2.me/theorems/362fcbdd-4fad-4c08-8a7c-3dbf2185131e
-- title:
--   Existence of a power for which the relative patch power induction rule holds
-- statement:
--   Let $s \ge 1$ be a natural number and let $\mathrm{discount}$ be a real number with $0 < \mathrm{discount} \le 1/2$. Then there is a natural number $\mathrm{power} \ge 2$ such that `RelativePatchPowerInductionRule s n₀ s discount power` holds, where $n_0$ = `scalarNativeDimension s` $= (s+1)(s+3)$.
--
--   Here `RelativePatchPowerInductionRule s n₀ stage τ E` is OpenAI's predicate `RelativePatchInductionRule s n₀ stage τ cutoff cost` with $\mathrm{cutoff}(p) = \mathrm{cost}(p) = (p+2)^E$. Unfolded, with $\mathrm{stage} = s$, $\tau = \mathrm{discount}$ and $E = \mathrm{power}$, it says: for all reals $p, a, \Lambda$ and every natural number $d_0$ with $p \ge 2$ and $e^{-p} \le a \le \Lambda \le 1$, if `RelativePatchAbsoluteRule s n₀ p a Λ d₀` holds, then for every finite nonempty type $X$ with decidable equality and $|X| \le p$, every $N : X \to \mathbb{N}$ with $e^{(p+2)^{E}} \le N_i$ for all $i$, every $f : \mathbb{Z}^X \to \mathbb{R}$ with values in $[0, 1]$ on the box $\prod_i [0, N_i)$ whose support in that box contains no nontrivial arithmetic progression of length $s + 2$ (`IntegerVectorAPFree`), every natural number $d$ and every `PolynomialPatch X s d` $A$ with `relativePatchComplexity A` $\le p$ (its number of slots plus $\log(1 + \text{kernel Lipschitz constant})$), `relativePatchDistinctWeights A` $\le s$ (its number of distinct weights) and $e^{-p} \le$ `relativePatchBoxScore N f a A`, the conclusion `RelativePatchSliceConclusion s N f ((1 - discount)^(s+1) * Λ) (d₀ + s * d) ((p+2)^E)` holds. `RelativePatchAbsoluteRule` (the base case on boxes of $n_0$ distinct comparable large primes), `relativePatchBoxScore` (the box average of $(f - a)$ times the patch value) and `RelativePatchSliceConclusion` (existence of a large residue box slice and a polynomial patch of bounded rank and complexity with large relative slice score) are defined by OpenAI.
--
--   Lean: `OAI.Erdos3.exists_manuscriptRelativePatchPower_s2`, which states OpenAI's `OAI.Erdos3.exists_manuscriptRelativePatchPower` (in `lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B034`, `OAIE3v2B148` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean (declaration OAI.Erdos3.exists_manuscriptRelativePatchPower)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B034
import Definitions.Def_OAIE3v2B148

section

namespace OAI

section

namespace Erdos3

theorem exists_manuscriptRelativePatchPower_s2 (s : ℕ) (hs : 1 ≤ s)
    (discount : ℝ) (hdiscount : 0 < discount) (hhalf : discount ≤ 1 / 2) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchPowerInductionRule s (VectorPolynomial.scalarNativeDimension s)
        s discount power := by
  sorry

end Erdos3

end

end OAI
end
