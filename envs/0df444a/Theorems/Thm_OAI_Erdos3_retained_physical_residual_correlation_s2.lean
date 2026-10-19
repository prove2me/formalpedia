-- Prove2me | Theorems.Thm_OAI_Erdos3_retained_physical_residual_correlation_s2
-- name    : OAI.Erdos3.retained_physical_residual_correlation_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:59:16.345331+00:00
-- url     : https://prove2.me/theorems/e21450b9-3046-4890-9098-48b6be4dbbb9
-- title:
--   Correlation bound for physical box residuals of two bounded functions at a good pair of affine parameters
-- statement:
--   Let $J, I$ be finite types with decidable equality, $k_0 \in J$, $D, r$ natural numbers, $\mathrm{anchor}, \mathrm{parLo}, \mathrm{parHi} : J \to \mathbb{Z}$, and $x, y \in \prod_j [\mathrm{parLo}(j), \mathrm{parHi}(j))$. Let $H : I \to \mathbb{R}$ with $H(i) > 0$ for all $i$, reals $L, C, \kappa, \delta$ with $L \ge 1$, $C \ge 1$, $\kappa > 0$, $0 \le \delta \le 1$, and a natural number $Q$. (All named objects are defined by OpenAI.) Assume:
--   - $|(\mathrm{anchor}(j) + D\, \mathrm{parLo}(j))/L| \le C$ and $|(\mathrm{anchor}(j) + D\, \mathrm{parHi}(j))/L| \le C$ for all $j$;
--   - $\kappa L \le D(r+1)$;
--   - $(x, y)$ is not a bad pair: `affineParameterBadPair D Q r anchor x y` fails, where that predicate holds when the absolute value of the gcd of the entries of $(\mathrm{anchor} + D y) - (\mathrm{anchor} + D x)$ exceeds $Q$, or $|y_j - x_j| \le r$ for every $j$;
--   - $2 C L^2 / H(i) \le \delta$ for all $i$;
--   - $4^{2 + \#\{j \ne k_0\}} \cdot \texttt{smoothPairRowLipschitz}\ k_0 \cdot \delta \le 1/2$, where `smoothPairRowLipschitz k₀` $= (\#\{j \ne k_0\} + 2) \cdot$ `probabilityProfileLipschitz`.
--
--   Let $\mathrm{origin} : \operatorname{Option} J \times I \to \mathbb{Z}$, let the scale of $(c, i)$ be $\mathrm{sc}(c, i)$ = `smoothPairCoefficientScale (H i) L c` ($H(i)$ for $c = \mathrm{none}$, $H(i)/L$ otherwise), and assume $\sum_z \prod_t \psi\bigl((z(t) - \mathrm{origin}(t))/\mathrm{sc}(t)\bigr) > 0$ (`shiftedSmoothProductMass`, $\psi$ OpenAI's smooth probability profile); let $\mathbb{P}$ = `smoothSourceFiniteWeights` be the normalized probability weights on $z : \operatorname{Option} J \times I \to \mathbb{Z}$ proportional to these products. Let $\mathrm{lo} : I \to \mathbb{Z}$ and $N : I \to \mathbb{N}$ with $Q \le N(i)$ for all $i$, let $\mathcal{B}$ = `translatedIntegerBox lo N` $= \mathrm{lo} + \prod_i ([0, N(i)) \cap \mathbb{Z})$, let $\mathrm{degree}$ be a natural number, and $f, g : \mathbb{Z}^I \to \mathbb{R}$ with values in $[0,1]$ on $\mathcal{B}$. Let $\eta, \rho, \mathrm{modLog}, \mathrm{dimLog}, \mathrm{accLog}$ be reals with $\rho \ge 0$, $\eta \le 1$, $\mathrm{modLog} \ge 0$, $e^{-\mathrm{accLog}} \le \eta$, $Q \le e^{\mathrm{modLog}}$, $\#I \le e^{\mathrm{dimLog}}$, $4 \le \rho H(i) \le 2N(i)$ for all $i$, $\exp(2\,\mathrm{degree} \cdot \mathrm{modLog} + \mathrm{accLog} + \mathrm{dimLog} + 1) \le \rho H(i)/4$ for all $i$, and $Q \le 2^{\mathrm{degree}}$.
--
--   Let $\mathcal{P}$ = `normalizedBoxPartitions N H ρ _ _` (for each $i$, OpenAI's partition of $[0, N(i))$ into progressions of comparable length $\lfloor \rho H(i)/2 \rfloor$), and for a function $u$ let $\mathrm{Res}(u)$ = `physicalBoxResidual lo N 𝒫 _ (boundedPrimePower Q) degree u`, which at a point $w$ equals $u(w)$ minus OpenAI's physical box truncation of $u$ (built from the partition and the moduli $p^{e_p}$ attached to the bounded primes $p$ of $Q$) if $w \in \mathcal{B}$, and $0$ otherwise. For $z$ and $t \in \prod_j [\mathrm{parLo}(j), \mathrm{parHi}(j))$ write $\mathrm{smp}_t(z)(i) = z(\mathrm{none}, i) + \sum_j (\mathrm{anchor}(j) + D t_j)\, z(\mathrm{some}\ j, i)$ (`smoothAffineSample`). Then
--   $$\Bigl| \mathbb{E}_{z \sim \mathbb{P}}\, \mathrm{Res}(f)(\mathrm{smp}_x(z)) \cdot \mathrm{Res}(g)(\mathrm{smp}_y(z)) \Bigr| \le \texttt{physicalResidualPairBudget lo N H k₀ Q C κ δ degree η ρ},$$
--   an explicit real quantity defined by OpenAI, equal to
--   $$\frac{(\#\mathcal{B})^2}{\prod_i H(i)^2} \Bigl( \mathrm{kc} \cdot (\eta\, \mathrm{tc})^2 + \bigl(\texttt{fullSmoothPairError}\ (\#I)\ k_0\ Q\ C\ \kappa\ \delta + \mathrm{kl} \cdot \rho\bigr)\, 2^{\#I} (1 + \eta\, \mathrm{tc}^2) \Bigr),$$
--   with $\mathrm{kc}$ = `smoothPairKernelCap (#I) k₀ C κ`, $\mathrm{kl}$ = `smoothPairKernelLip (#I) k₀ C κ` and $\mathrm{tc}$ = `residueTruncationCap (BoundedPrime Q) degree η`.
--
--   Lean: `OAI.Erdos3.retained_physical_residual_correlation_s2`, which states OpenAI's `OAI.Erdos3.retained_physical_residual_correlation` (in `lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean (declaration OAI.Erdos3.retained_physical_residual_correlation)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem retained_physical_residual_correlation_s2 {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ)
    (x y : ∀ j, Finset.Ico (parLo j) (parHi j))
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (hgood : ¬ affineParameterBadPair D Q r anchor (fun j => (x j).val) (fun j => (y j).val))
    (hmesh : ∀ i, 2 * C * L ^ 2 / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k0}) * smoothPairRowLipschitz k0 * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f (smoothAffineSample (fun j => anchor j + (D : ℤ) * (x j).val) z.val) *
        physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree g (smoothAffineSample (fun j => anchor j + (D : ℤ) * (y j).val) z.val))| ≤
      physicalResidualPairBudget lo N H k0 Q C κ δ degree eta ρ := by
  sorry

end Erdos3

end

end OAI
end
