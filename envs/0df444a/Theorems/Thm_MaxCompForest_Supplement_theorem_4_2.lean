-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_4_2
-- name    : MaxCompForest.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:24:30.454096+00:00
-- url     : https://prove2.me/theorems/160cadfe-0e8f-4150-9d0c-a327686c9823
-- title:
--   Theorem 4.2 — diagonal-mass candidate coreset for $k$-principal determinants
-- statement:
--   Let $K\in\mathbb R^{m\times m}$ be a PSD contraction ($K$ symmetric, $0\preceq K\preceq I$) with $r_0=\mathrm{tr}\,K>0$, let $2\le k\le m$, $0<\varepsilon\le1$ and $a\ge\max\{1,m/r_0\}$, and put
--   $$M=\min\Big\{m,\ \Big\lceil a\Big((k-1)+\frac{2k(k-1)}{\varepsilon}\Big)\Big\rceil+1\Big\}.\tag{4.2}$$
--   Let $T$ be any set of $M$ indices of largest diagonal entries of $K$, with arbitrary tie-breaking. Then
--   $$\max_{F\subseteq T,\ |F|=k}\det K_F\ \ge\ \Big(1-\frac\varepsilon2\Big)\max_{|F|=k}\det K_F\ \ge\ \frac{1}{1+\varepsilon}\max_{|F|=k}\det K_F .$$
--   Moreover:
--
--   1. the candidate size is $O(ak^2/\varepsilon)$: $M\le C_1ak^2/\varepsilon$ for an absolute $C_1$;
--   2. for rational $K$, $a$, $\varepsilon$, a deterministic algorithm enumerates the $k$-subsets of such a $T$ exactly and returns one of largest minor in time $(C_2ak/\varepsilon)^k(L+2)^b$, with absolute $C_2$ and $b$, where $L$ is the total binary input length.
--
--   For the transfer-current kernel of a graph, $\det K_F$ is the probability that a random spanning tree contains $F$, which turns this into the density-based approximation algorithm of Corollary 4.3.
--
--   **Formalization Note** The contraction condition is a promise of the algorithmic clause. Machines are Mathlib's multi-stack Turing machines with the base mission's binary encoders.
--
--   Differences from the source:
--   - encoding: a ≥ max{1, m/r₀} → 1 ≤ a and m ≤ a·tr K; reason: tr K > 0, so the division clears
--   - encoding: "Retain the M largest diagonal indices, with arbitrary tie-breaking" → every T with |T| = M and K_uu ≤ K_tt for t ∈ T, u ∉ T; reason: this is exactly the set of admissible retained sets
--   - encoding: max_{|F|=k} det K_F → a bound against every k-set F; reason: the maximum over finitely many sets
--   - encoding: candidate size O(ak²/ε) → ∃ absolute C₁ > 0 with M ≤ C₁ a k²/ε; reason: the constant is absolute
--   - reading: "exact enumeration takes (O(ak/ε))^k poly(L) time" → one TM2 machine with absolute C₂, b; it outputs k distinct indices inside some admissible retained set T, of largest minor among the k-subsets of T, within ⌈(C₂ak/ε)^k (L+2)^b⌉ steps; reason: exact enumeration of the k-subsets of the retained set; poly(L) with absolute exponent
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 4.2 and (4.2), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MaxCompForest_encIndices
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_MaxCompForest_Supplement_principalDet
import Definitions.Def_MaxCompForest_Supplement_encCoresetIn
open OnlineCRS.Combine (Sym)
open CFLOutliers (OutputsWithin)
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem 4.2 (Diagonal-mass candidate coreset).** Let `K ∈ ℝ^{m×m}` be a PSD contraction (`0 ⪯ K ⪯ I`) with
`r₀ = tr K > 0`, `2 ≤ k ≤ m`, `0 < ε ≤ 1`, `a ≥ max{1, m/r₀}`, and
`M = min{m, ⌈a((k−1) + 2k(k−1)/ε)⌉ + 1}` (4.2). For every set `T` of `M` indices of largest diagonal entries (any
tie-breaking), the largest `k`-principal determinant of `K` on `T` is at least `(1 − ε/2) max_{|F|=k} det K_F`, hence at
least `max_{|F|=k} det K_F / (1+ε)`. The candidate size is `O(a k²/ε)`. For rational `K`, `a`, `ε`, exact enumeration
takes `(O(ak/ε))^k poly(L)` time.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 4.2 and (4.2), p.26.

**Formalization Note.** "Retain the `M` largest diagonal indices, with arbitrary tie-breaking" is every `T` with
`|T| = M` and `K_uu ≤ K_tt` for `t ∈ T`, `u ∉ T`. `a ≥ m/r₀` has its division cleared (`m ≤ a · tr K`). The maximum
over `|F| = k` is a bound against every `k`-set. The algorithmic clause: one machine and absolute `C₂`, `b`; on the
binary word of `(m, k, a, ε, K)` it outputs a list of `k` distinct indices inside some admissible retained set `T`
whose minor is the largest among the `k`-subsets of `T`, within `⌈(C₂ a k/ε)^k (L+2)^b⌉` steps; the contraction
condition is a promise. -/
theorem theorem_4_2 :
    ∃ (C₁ C₂ : ℝ) (Mach : Turing.TM2ComputableAux Sym Sym) (b : ℕ), 0 < C₁ ∧ 0 < C₂ ∧
      (∀ (m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ) (k : ℕ) (ε a : ℝ),
        K.PosSemidef → (1 - K).PosSemidef → 0 < K.trace → 2 ≤ k → k ≤ m → 0 < ε → ε ≤ 1 →
        1 ≤ a → (m : ℝ) ≤ a * K.trace →
        ((min m (⌈a * (((k : ℝ) - 1) + 2 * k * ((k : ℝ) - 1) / ε)⌉₊ + 1) : ℕ) : ℝ) ≤ C₁ * a * k ^ 2 / ε ∧
        ∀ T : Finset (Fin m), T.card = min m (⌈a * (((k : ℝ) - 1) + 2 * k * ((k : ℝ) - 1) / ε)⌉₊ + 1) →
          (∀ t ∈ T, ∀ u ∉ T, K u u ≤ K t t) →
          ∃ F ⊆ T, F.card = k ∧
            (∀ F' : Finset (Fin m), F'.card = k → (1 - ε / 2) * principalDet K F' ≤ principalDet K F) ∧
            (∀ F' : Finset (Fin m), F'.card = k → principalDet K F' / (1 + ε) ≤ principalDet K F)) ∧
      (∀ (m : ℕ) (K : Fin m → Fin m → ℚ) (k : ℕ) (ε a : ℚ),
        (Matrix.of fun i j => (K i j : ℝ)).PosSemidef → (1 - Matrix.of fun i j => (K i j : ℝ)).PosSemidef →
        0 < (Matrix.of fun i j => (K i j : ℝ)).trace → 2 ≤ k → k ≤ m → 0 < ε → ε ≤ 1 → 1 ≤ a →
        (m : ℝ) ≤ (a : ℝ) * (Matrix.of fun i j => (K i j : ℝ)).trace →
        ∃ F : List (Fin m), F.Nodup ∧ F.length = k ∧
          (∃ T : Finset (Fin m),
            T.card = min m (⌈(a : ℝ) * (((k : ℝ) - 1) + 2 * k * ((k : ℝ) - 1) / (ε : ℝ))⌉₊ + 1) ∧
            (∀ t ∈ T, ∀ u ∉ T, K u u ≤ K t t) ∧ F.toFinset ⊆ T ∧
            ∀ F' ⊆ T, F'.card = k →
              principalDet (Matrix.of fun i j => (K i j : ℝ)) F' ≤
                principalDet (Matrix.of fun i j => (K i j : ℝ)) F.toFinset) ∧
          OutputsWithin Mach (encCoresetIn K a ε k) (MaxCompForest.encIndices F)
            ⌈(C₂ * (a : ℝ) * k / (ε : ℝ)) ^ k * (((encCoresetIn K a ε k).length : ℝ) + 2) ^ b⌉₊) := by sorry

end MaxCompForest.Supplement
