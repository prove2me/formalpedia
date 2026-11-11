-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_eq_5
-- name    : LowRankMisspec.RankOne.eq_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:07.745506+00:00
-- url     : https://prove2.me/theorems/dbc0339d-2467-4fbe-adc0-60aed3980928
-- title:
--   §A.2, Eq. (5) — $\|\otimes_t p_t-\otimes_t r_t\|_1\le\sqrt{2\sum_t\chi^2(p_t\|r_t)}$
-- statement:
--   For rows $p_t,r_t\in\Delta([\sigma])$, $t=1,\dots,T$,
--   $$\Big\|\bigotimes_t p_t-\bigotimes_t r_t\Big\|_1\le\sqrt{2\sum_t\chi^2(p_t\|r_t)},$$
--   where $\chi^2(p\|r)=\sum_{x:r[x]>0}(p[x]-r[x])^2/r[x]$, taken to be infinite unless $p$ is supported on the support of $r$. It controls the quadratic accumulation of the repaired rows in Lemma 5.2's proof.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: an inequality between reals with χ² possibly +∞ → ENNReal.ofReal ‖·‖₁ ≤ (2 · Σ_t χ²)^(1/2) in ℝ≥0∞, with ⊤^(1/2) = ⊤; reason: represents the infinite value; when every χ² is finite it is the real inequality
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 17 (PDF 18), §A.2, Eq. (5)

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Divergences

namespace LowRankMisspec.RankOne

/-- §A.2, Eq. (5): for rows `p_t, r_t ∈ Δ([σ])`,
`‖⊗_t p_t − ⊗_t r_t‖₁ ≤ √(2 Σ_t χ²(p_t ‖ r_t))`, in `ℝ≥0∞` (the right side is `+∞` when some
`p_t` is not supported on the support of `r_t`). -/
theorem eq_5 {σ T : ℕ} (p r : Fin T → Fin σ → ℝ) (hp : ∀ t, IsLaw (p t)) (hr : ∀ t, IsLaw (r t)) :
    ENNReal.ofReal (l1 (prodLaw p) (prodLaw r)) ≤
      (2 * ∑ t, chi2 (p t) (r t)) ^ (1 / 2 : ℝ) := by sorry

end LowRankMisspec.RankOne
