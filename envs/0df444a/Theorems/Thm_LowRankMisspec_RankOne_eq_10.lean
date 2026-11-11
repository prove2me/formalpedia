-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_eq_10
-- name    : LowRankMisspec.RankOne.eq_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:10.138274+00:00
-- url     : https://prove2.me/theorems/571e1a72-b6ed-406b-a25e-eac5b807ae48
-- title:
--   Appendix D, Eq. (10) — total variation as the expectation of the bounded loss $f_{R,H}$
-- statement:
--   For laws $R,H$ on $[\sigma]^T$, with $f_{R,H}(x)=(1-H[x]/R[x])_+$ if $R[x]>0$ and $0$ if $R[x]=0$:
--   $0\le f_{R,H}\le1$, and
--   $$\mathbb E_{X\sim R}f_{R,H}(X)=\sum_{x:R[x]>0}(R[x]-H[x])_+=\sum_x(R[x]-H[x])_+=\tfrac12\|R-H\|_1.$$
--   Samples from $R$ with their exact $R$-probabilities therefore estimate distances by averaging a loss in $[0,1]$; Corollary D.2 rests on this.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: E_{X∼R} f_{R,H}(X) → Σ_x R x · tvLoss R H x; reason: expectation over a finite law
--   - encoding: the second case of f_{R,H} is R[x] = 0 → tvLoss takes 0 whenever ¬(0 < R x); reason: for a law, R x ≥ 0, so ¬(0 < R x) is R x = 0
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 32 (PDF 33), Appendix D, Eq. (10)

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Divergences

namespace LowRankMisspec.RankOne

/-- Appendix D, Eq. (10) (total variation as the expectation of a bounded loss): for laws `R, H`
on `[σ]^T`, `0 ≤ f_{R,H} ≤ 1` and
`E_{X∼R} f_{R,H}(X) = Σ_{x : R[x] > 0} (R[x] − H[x])₊ = Σ_x (R[x] − H[x])₊ = ½ ‖R − H‖₁`. -/
theorem eq_10 {σ T : ℕ} (R H : Str σ T → ℝ) (hR : IsLaw R) (hH : IsLaw H) :
    (∀ x, 0 ≤ tvLoss R H x ∧ tvLoss R H x ≤ 1) ∧
    ∑ x, R x * tvLoss R H x = ∑ x ∈ Finset.univ.filter (fun x => 0 < R x), max (R x - H x) 0 ∧
    ∑ x ∈ Finset.univ.filter (fun x => 0 < R x), max (R x - H x) 0 = ∑ x, max (R x - H x) 0 ∧
    ∑ x, max (R x - H x) 0 = 1 / 2 * l1 R H := by sorry

end LowRankMisspec.RankOne
