-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_theorem_7_1
-- name    : MCAListDecoding.PowersGenerator.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:06.10727+00:00
-- url     : https://prove2.me/theorems/b0718e6d-1a9d-4aff-a55f-598fb9d1f220
-- title:
--   Theorem 7.1 — explicit gap-dependent bound ε_MCA(γ) ≤ (15d/|S|)·max{1, γn, γ/(J_h(δ_C) − γ)}
-- statement:
--   Let $F$ be a finite field, $\Sigma$ a finite-dimensional $F$-vector space, $C\subseteq\Sigma^n$ a nonzero $F$-linear code with minimum distance $\Delta_C$ and relative distance $\delta_C=\Delta_C/n$, $d\ge1$, $S\subseteq F$ a nonempty seed set, $h=d+2$, and $\gamma\in[0,1]$ real; write $\gamma'=\lfloor\gamma n\rfloor/n$ (the paper replaces $\gamma$ by $\gamma'$ throughout the hypotheses and the bound). For words $u_0,\dots,u_d\in\Sigma^n$, $B\subseteq S$ is the set of MCA-bad seeds at radius $\gamma$. If $2\gamma'n<\Delta_C$ and $\gamma'<J_h(\delta_C)$, then for every $u_0,\dots,u_d$
--   $$\frac{|B|}{|S|}\le\frac{15d}{|S|}\max\Big\{1,\ \gamma'n,\ \frac{\gamma'}{J_h(\delta_C)-\gamma'}\Big\},$$
--   i.e. $G_d$ has mutual correlated agreement for $C$ with error $\epsilon_{\mathrm{MCA}}(\gamma)\le\xi_{C,d,|S|}(\gamma)$.
--
--   Differences from the source:
--   - encoding: real γ ∈ [0,1], replaced by ⌊γn⌋/n throughout the hypotheses and the bound → roundRadius n γ = ⌊γn⌋₊/n in the hypotheses and the bound; the bad-seed event uses |T| ≥ n(1−γ) with the real γ; reason: |T| ≥ n(1−γ) holds iff |T| ≥ n − ⌊γn⌋ iff |T| ≥ n(1 − ⌊γn⌋/n), so the event is the same; the paper's stated rounding rule
--   - encoding: ϵ_MCA(γ) ≤ bound (the maximal fraction of MCA-bad seeds of S over all word tuples) → for every u : Fin (d+1) → Fin n → Alph, (badSeeds C d γ u S).card / S.card ≤ bound; reason: Definition 3.4 and the remark after Definition 4.1: bounding |B|/|S| uniformly in U bounds ϵ_MCA(γ)
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Theorem 7.1, p. 40

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code

namespace MCAListDecoding.PowersGenerator

/-- Theorem 7.1 (explicit gap-dependent bound), p. 40. `Alph` (the paper's `Σ`) is a
finite-dimensional vector space over the finite field `F`, `C ⊆ Alph^n` a nonzero `F`-linear code,
`d ≥ 1`, `S ⊆ F` nonempty, `h = d + 2`, `γ ∈ [0, 1]` real and `γ' = ⌊γ n⌋ / n` (the paper's rule:
replace `γ` by `⌊γ n⌋/n` throughout the hypotheses and the bound). If `2 γ' n < Δ_C` and
`γ' < J_h(δ_C)`, then for all words `u_0, …, u_d` the fraction of MCA-bad seeds of `S` is at most
`(15 d/|S|) · max{1, γ' n, γ'/(J_h(δ_C) - γ')}`. -/
theorem theorem_7_1 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hΔ : 2 * roundRadius n γ * n < (minDist C : ℝ))
    (hJ : roundRadius n γ < johnsonRadius (d + 2) (relDist C)) :
    ∀ u : Fin (d + 1) → Fin n → Alph,
      ((badSeeds C d γ u S).card : ℝ) / S.card ≤
        15 * d / S.card * max (max 1 (roundRadius n γ * n))
          (roundRadius n γ / (johnsonRadius (d + 2) (relDist C) - roundRadius n γ)) := by sorry

end MCAListDecoding.PowersGenerator
