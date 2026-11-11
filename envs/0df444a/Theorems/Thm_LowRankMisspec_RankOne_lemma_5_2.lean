-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_lemma_5_2
-- name    : LowRankMisspec.RankOne.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:17:46.479415+00:00
-- url     : https://prove2.me/theorems/5f16dc3f-1d46-4c96-bfa8-e5a262619a07
-- title:
--   Lemma 5.2 — frozen-trajectory closeness: $\Pr_{X\sim P}\{\|R_X-Q\|_1\le 96\|P-Q\|_1\}\ge 1/2$
-- statement:
--   For every law $P$ on $[\sigma]^T$ and every product law $Q=\bigotimes_t q_t$ (rows $q_t\in\Delta([\sigma])$, no full-support condition),
--   $$\Pr_{X\sim P}\big\{\|R_X-Q\|_1\le 96\,\|P-Q\|_1\big\}\ge\tfrac12,$$
--   where $R_x[y]=\prod_{t=1}^T P[y_t\mid x_{<t}]$ is the frozen-trajectory product law, defined for $P[x]>0$. The constant $96$ does not depend on $T$ or $\sigma$. This is the main ingredient of Theorem 5.1: applied to a closest product law it shows that one of $O(\log(1/\delta))$ reference trajectories yields a product within $96\,d_1(P)$ of it.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: a distribution P ∈ Δ([σ]^T) → a real function P on Fin T → Fin σ with IsLaw P (nonnegative, summing to 1); reason: the simplex written out; same instances
--   - encoding: Pr_{X∼P}{…}, with R_X defined for P[X] > 0 → the sum of P x over the strings x with P x > 0 and ‖R_x − Q‖₁ ≤ 96‖P − Q‖₁; reason: strings with P x = 0 carry no mass; same statement
--   - encoding: every product law Q → Q = prodLaw q for rows q t that are laws on Fin σ; reason: a product law is the product of its rows
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 8 (PDF 9), Lemma 5.2

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Frozen

namespace LowRankMisspec.RankOne

/-- Lemma 5.2 (frozen-trajectory closeness): for every law `P` on `[σ]^T` and every product law
`Q = ⊗_t q_t` (rows `q_t ∈ Δ([σ])`), `Pr_{X∼P}{‖R_X − Q‖₁ ≤ 96 ‖P − Q‖₁} ≥ 1/2`, the
probability being the `P`-mass of the strings `x` with `P[x] > 0` (where `R_x` is defined) that
satisfy the inequality. -/
theorem lemma_5_2 {σ T : ℕ} (P : Str σ T → ℝ) (hP : IsLaw P) (q : Fin T → Fin σ → ℝ)
    (hq : ∀ t, IsLaw (q t)) :
    (1 / 2 : ℝ) ≤ ∑ x ∈ Finset.univ.filter (fun x =>
        0 < P x ∧ l1 (frozenLaw P x) (prodLaw q) ≤ 96 * l1 P (prodLaw q)), P x := by sorry

end LowRankMisspec.RankOne
