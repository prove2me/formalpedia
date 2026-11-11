-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_corollary_7_2
-- name    : MCAListDecoding.PowersGenerator.corollary_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:06.460653+00:00
-- url     : https://prove2.me/theorems/c06ee200-aef2-4fe8-afd8-a36767cb3442
-- title:
--   Corollary 7.2 (= Theorem 1) — powers-generator MCA error ≤ 15d·max{1,nγ}/|S| up to J_{d+2}(δ_C) − 1/n and ≤ 24d·max{1,nγ}/|S| below δ_C/2
-- statement:
--   Let $F$ be a finite field, $\Sigma$ a finite-dimensional $F$-vector space, $C\subseteq\Sigma^n$ a nonzero $F$-linear code with minimum distance $\Delta_C$ and relative distance $\delta_C=\Delta_C/n$, $d\ge1$, $S\subseteq F$ a nonempty seed set, $h=d+2$, and $\gamma\in[0,1]$ real; write $\gamma'=\lfloor\gamma n\rfloor/n$ (the paper replaces $\gamma$ by $\gamma'$ throughout the hypotheses and the bound). For words $u_0,\dots,u_d\in\Sigma^n$, $B\subseteq S$ is the set of MCA-bad seeds at radius $\gamma$. Then:
--
--   1. (In the setting of Theorem 7.1.) If $2\gamma'n<\Delta_C$, $\gamma'<J_h(\delta_C)$ and $n\,(J_h(\delta_C)-\gamma')\ge1$ — which holds in particular when $\gamma'\le J_h(\delta_C)-1/n$ — then for every $u_0,\dots,u_d$
--   $$\frac{|B|}{|S|}\le\frac{15d}{|S|}\max\{1,\ n\gamma'\}.$$
--   2. If $J_h(\delta_C)\ge\delta_C/2$, then for every $\gamma$ with $\gamma'<\delta_C/2$ and every $u_0,\dots,u_d$
--   $$\frac{|B|}{|S|}\le\frac{24d}{|S|}\max\{1,\ n\gamma'\}.$$
--
--   This is Corollary 7.2 (p. 43), the formal version of Theorem 1 (p. 6): Theorem 1.1 is part 2, and Theorem 1.2 ($J_{d+2}(\delta_C)<\delta_C/2$, $\gamma\le J_{d+2}(\delta_C)-1/n$) is contained in part 1.
--
--   Differences from the source:
--   - encoding: real γ ∈ [0,1], replaced by ⌊γn⌋/n throughout the hypotheses and the bound → roundRadius n γ = ⌊γn⌋₊/n in the hypotheses and the bound; the bad-seed event uses |T| ≥ n(1−γ) with the real γ; reason: |T| ≥ n(1−γ) holds iff |T| ≥ n − ⌊γn⌋ iff |T| ≥ n(1 − ⌊γn⌋/n), so the event is the same; the paper's stated rounding rule
--   - encoding: ϵ_MCA(γ) ≤ bound (the maximal fraction of MCA-bad seeds of S over all word tuples) → for every u : Fin (d+1) → Fin n → Alph, (badSeeds C d γ u S).card / S.card ≤ bound; reason: Definition 3.4 and the remark after Definition 4.1: bounding |B|/|S| uniformly in U bounds ϵ_MCA(γ)
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Corollary 7.2, p. 43 (formal version of Theorem 1, p. 6)

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code

namespace MCAListDecoding.PowersGenerator

/-- Corollary 7.2 (uniform scaling), p. 43; the formal version of Theorem 1, p. 6. Setting of
Theorem 7.1: `Alph` (the paper's `Σ`) a finite-dimensional vector space over the finite field
`F`, `C ⊆ Alph^n` a nonzero `F`-linear code (so `δ_C = Δ_C/n` is defined), `d ≥ 1`, `S ⊆ F`
nonempty, `h = d + 2`, `γ ∈ [0, 1]` real, `γ' = ⌊γ n⌋/n` in the hypotheses and the bound.
1. If `2 γ' n < Δ_C`, `γ' < J_h(δ_C)` and `n (J_h(δ_C) - γ') ≥ 1`, then every word tuple has at most
   a `(15 d/|S|) · max{1, n γ'}` fraction of MCA-bad seeds in `S`.
2. If `J_h(δ_C) ≥ δ_C/2` and `γ' < δ_C/2`, then the fraction is at most `(24 d/|S|) · max{1, n γ'}`. -/
theorem corollary_7_2 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (2 * roundRadius n γ * n < (minDist C : ℝ) →
      roundRadius n γ < johnsonRadius (d + 2) (relDist C) →
      1 ≤ (n : ℝ) * (johnsonRadius (d + 2) (relDist C) - roundRadius n γ) →
      ∀ u : Fin (d + 1) → Fin n → Alph,
        ((badSeeds C d γ u S).card : ℝ) / S.card ≤
          15 * d / S.card * max 1 ((n : ℝ) * roundRadius n γ)) ∧
    (relDist C / 2 ≤ johnsonRadius (d + 2) (relDist C) →
      roundRadius n γ < relDist C / 2 →
      ∀ u : Fin (d + 1) → Fin n → Alph,
        ((badSeeds C d γ u S).card : ℝ) / S.card ≤
          24 * d / S.card * max 1 ((n : ℝ) * roundRadius n γ)) := by sorry

end MCAListDecoding.PowersGenerator
