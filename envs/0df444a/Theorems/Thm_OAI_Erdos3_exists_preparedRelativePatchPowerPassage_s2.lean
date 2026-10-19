-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_preparedRelativePatchPowerPassage_s2
-- name    : OAI.Erdos3.exists_preparedRelativePatchPowerPassage_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:13:51.31347+00:00
-- url     : https://prove2.me/theorems/aebc0fd1-0187-4243-a438-0070f2838ef9
-- title:
--   A power induction rule yields a prepared relative patch power passage
-- statement:
--   Let $s, n_0, \mathrm{stage}, \mathrm{childExponent} \in \mathbb{N}$ and $\mathrm{discount} \in \mathbb{R}$ with $1 \le s$, $2 \le \mathrm{childExponent}$ and $0 < \mathrm{discount} \le 1$, and assume `RelativePatchPowerInductionRule s n₀ stage discount childExponent` (the rule `RelativePatchInductionRule` with cutoff and cost both $p \mapsto (p+2)^{\mathrm{childExponent}}$). Then there are $\mathrm{requiredPower}, \mathrm{precisionPower} \in \mathbb{N}$ such that for every $\mathrm{preparationPower} \ge 2$ there is $\mathrm{passagePower} \ge 2$ with `PreparedRelativePatchPowerPassage s n₀ stage discount requiredPower precisionPower preparationPower passagePower`.
--
--   `PreparedRelativePatchPowerPassage s n₀ stage discount requiredPower precisionPower preparationPower passagePower` is the proposition: for all reals $p \ge 2$ and $e^{-p} \le a \le \Lambda \le 1$ and $d_0 \in \mathbb{N}$ with `RelativePatchAbsoluteRule s n₀ p a Λ d₀`; every $n_X$ with $0 < n_X \le p$; every $N : \mathrm{Fin}\ n_X \to \mathbb{N}$ with $\exp((p+2)^{\mathrm{passagePower}}) \le N_i$; every $f : \mathbb{Z}^{n_X} \to [0,1]$ whose support in the box $\prod_i[0,N_i)$ is `IntegerVectorAPFree` of length $s+2$ (no nontrivial $(s+2)$-term arithmetic progression of integer vectors); all $D, E, m$ with $0 < D$, $0 < m \le s$; every `oldPatch : PolynomialPatch (Fin nX) s (D + E)` with `F : oldPatch.LowestLayerModel m`, all weights beyond the first $D$ exceeding $m$, `relativePatchComplexity oldPatch` $\le p$, at most $\mathrm{stage}+1$ distinct weights, and `relativePatchBoxScore N f a oldPatch` $\ge e^{-p}$; every `L : RankPreparationFamily (Fin nX) (Fin D) m` with `L.Sized D (m * D)`, `L.PreparedHeights ((p + 2) ^ preparationPower) R` for $R = $ `preparedRoundedRank p requiredPower` $= \lceil \exp((p+2)^{\mathrm{requiredPower}})\rceil$, ranks summing to at most $mD$, every layer having at most `preparationCoordinateCap m D (m * D)` coordinates, and `HasLayerSamplingRank (j+1) N R` for every layer's space and polynomial; and all integer polynomials $ip_i$ of total degree at most $m$, $c \in \mathbb{R}^D$ and a vector polynomial $\mathrm{err}$ of degree at most $m$ with `ofCoordinates` of `F.normalizedOrigin` equal to `L.polynomial + integerCoordinates ip + (1 ⊗ c) + err` and $|\mathrm{err}(x)_i| \le \exp(-(p+2)^{\mathrm{precisionPower}})$ on the box — `RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ) (d₀ + s * (D + E)) ((p + 2) ^ passagePower)` holds.
--
--   Here `RelativePatchSliceConclusion s N f target rankBound cost` asserts a stride $q > 0$, a residue box slice of $N$ with stride $q$ and all lengths at least $e^{-\mathrm{cost}} N_i$, and a `PolynomialPatch` of rank at most $\mathrm{rankBound}$ with `relativePatchComplexity` at most $\mathrm{cost}$ whose slice score (the mean over the slice of $(f - \mathrm{target})$ times the patch value) is at least $e^{-\mathrm{cost}}$. `RelativePatchAbsoluteRule s n₀ p a Λ d₀` says: for every injective $N : \mathrm{Fin}\ n_0 \to$ primes with $N_i \le 2^{n_0+1}N_j$ and $e^p \le N_i$ and every $f$ with values in $[0,1]$ on the box, $(s+2)$-AP-free support and box mean at least $a$, `RelativePatchSliceConclusion s N f Λ d₀ p` holds. `RelativePatchInductionRule s n₀ stage τ cutoff cost` says: for all $p \ge 2$, $e^{-p} \le a \le \Lambda \le 1$ with the absolute rule for $d_0$, every nonempty finite type $X$ with $|X| \le p$, $N$ with $e^{\mathrm{cutoff}(p)} \le N_i$, $f$ with values in $[0,1]$ on the box and $(s+2)$-AP-free support (no lower bound on its mean), and polynomial patch $A$ of rank $d$ with complexity at most $p$, at most `stage` distinct weights and box score at least $e^{-p}$, `RelativePatchSliceConclusion s N f ((1-τ)^(stage+1) * Λ) (d₀ + s * d) (cost p)` holds. `PolynomialPatch`, `LowestLayerModel`, `RankPreparationFamily`, `Sized`, `PreparedHeights` and `HasLayerSamplingRank` are OpenAI's definitions.
--
--   Lean: `OAI.Erdos3.exists_preparedRelativePatchPowerPassage_s2`, which states OpenAI's `OAI.Erdos3.exists_preparedRelativePatchPowerPassage` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativePositivePassage.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B258` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativePositivePassage.lean (declaration OAI.Erdos3.exists_preparedRelativePatchPowerPassage)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B258

section

namespace OAI

section

namespace Erdos3
open VectorPolynomial Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal TensorProduct
attribute [local irreducible] integerBox
  AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_preparedRelativePatchPowerPassage_s2
    (s n₀ stage childExponent : ℕ) (discount : ℝ)
    (hs : 1 ≤ s) (_hchildExponent : 2 ≤ childExponent)
    (hdiscount : 0 < discount) (hdiscountOne : discount ≤ 1)
    (ih : RelativePatchPowerInductionRule s n₀ stage discount childExponent) :
    ∃ requiredPower precisionPower : ℕ,
      ∀ preparationPower : ℕ, 2 ≤ preparationPower →
        ∃ passagePower : ℕ, 2 ≤ passagePower ∧
          PreparedRelativePatchPowerPassage s n₀ stage discount
            requiredPower precisionPower preparationPower passagePower := by
  sorry

end Erdos3

end

end OAI
end
