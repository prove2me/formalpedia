-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_relativePatch_scalarBase_fin_power_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_relativePatch_scalarBase_fin_power_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:26:05.951258+00:00
-- url     : https://prove2.me/theorems/d1fa1238-615a-4254-8cea-0b3cd1b503ee
-- title:
--   The stage-zero relative patch induction rule holds with power cutoff and cost (p+2)^U
-- statement:
--   Let $s$ be a natural number and $\tau$ (called `discount` in Lean) a real number with $0 < \tau \le 1/2$. Then there is a natural number $U \ge 2$ such that `RelativePatchFinInductionRule s (scalarNativeDimension s) 0 τ (fun p => (p + 2) ^ U) (fun p => (p + 2) ^ U)` holds, where `scalarNativeDimension s` $= (s+1)(s+3)$.
--
--   Here, with $n_0$ = `scalarNativeDimension s`, cutoff$(p)$ = cost$(p) = (p+2)^U$ and stage $=0$, `RelativePatchFinInductionRule` (defined by OpenAI) is the following statement. For all reals $p, a, \Lambda$ and every natural number $d_0$ with $2 \le p$, $e^{-p} \le a \le \Lambda \le 1$, if `RelativePatchAbsoluteRule s n₀ p a Λ d₀` holds, then for every natural number $n$ with $0 < n \le p$, every $N : \{0,\dots,n-1\} \to \mathbb{N}$ with $e^{\mathrm{cutoff}(p)} \le N_i$ for all $i$, and every $f : \mathbb{Z}^n \to \mathbb{R}$ with $f(x) \in [0,1]$ on the box $\prod_i [0, N_i)$ such that the set $\{x \in \text{box} : f(x) \ne 0\}$ is `IntegerVectorAPFree` of length $s+2$ (for all $a, d \in \mathbb{Z}^n$ with $d \ne 0$ some $a + id$, $0 \le i < s+2$, lies outside the set), and for every $d$ and every `PolynomialPatch (Fin n) s d` $A$ with `relativePatchComplexity A` $\le p$, `relativePatchDistinctWeights A` $\le 0$ (the number of distinct values of its weight function $\{0,\dots,d-1\} \to \mathbb{N}$, so this forces $d = 0$) and
--   $$e^{-p} \le \texttt{relativePatchBoxScore N f a A} = \mathop{\mathbb{E}}_{x \in \text{box}} (f(x) - a)\,A(x),$$
--   the conclusion `RelativePatchSliceConclusion s N f ((1 - τ) ^ 1 * Λ) (d₀ + s * d) (cost p)` holds: there exist $q > 0$, a residue box slice $S$ (start points and lengths with $\mathrm{start}_i + qj < N_i$ for $j < \mathrm{length}_i$), a natural number $d' \le d_0 + sd$ and a `PolynomialPatch (Fin n) s d'` $A'$ with $e^{-\mathrm{cost}(p)} N_i \le \mathrm{length}_i$ for all $i$, `relativePatchComplexity A'` $\le \mathrm{cost}(p)$, and $e^{-\mathrm{cost}(p)} \le$ `relativePatchSliceScore S f ((1-τ)Λ) A'` (the average over the slice of $(f - (1-\tau)\Lambda)$ times the patch value at the slice coordinates).
--
--   `RelativePatchAbsoluteRule s n₀ p a Λ d₀` (defined by OpenAI) says: for every $N : \{0,\dots,n_0-1\} \to \mathbb{N}$ consisting of distinct primes with $N_i \le 2^{n_0+1}N_j$ for all $i,j$ and $e^p \le N_i$ for all $i$, and every $f : \mathbb{Z}^{n_0} \to \mathbb{R}$ with values in $[0,1]$ on the box, whose support in the box is `IntegerVectorAPFree` of length $s+2$ and whose box average is at least $a$, `RelativePatchSliceConclusion s N f Λ d₀ p` holds. `relativePatchComplexity A` $= d + \log(1 + \mathrm{Lip})$, where Lip is the Lipschitz constant of the patch kernel; a `PolynomialPatch X s d` is OpenAI's structure consisting of monotone weights in $[1, s]$, a polynomial form in the slots and a patch kernel, and $A(x)$ denotes its value.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_relativePatch_scalarBase_fin_power_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_relativePatch_scalarBase_fin_power` (in `lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchScalarBaseFin.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B149` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchScalarBaseFin.lean (declaration OAI.Erdos3.VectorPolynomial.exists_relativePatch_scalarBase_fin_power)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B149

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_relativePatch_scalarBase_fin_power_s2 (s : ℕ)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ U : ℕ, 2 ≤ U ∧
      RelativePatchFinInductionRule s (scalarNativeDimension s) 0 discount
        (fun p => (p + 2) ^ U) (fun p => (p + 2) ^ U) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
