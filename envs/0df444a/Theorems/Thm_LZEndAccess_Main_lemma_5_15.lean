-- Prove2me | Theorems.Thm_LZEndAccess_Main_lemma_5_15
-- name    : LZEndAccess.Main.lemma_5_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:34:48.324742+00:00
-- url     : https://prove2.me/theorems/025bbe71-e2e0-4cc2-978d-39b9f7362611
-- title:
--   Lemma 5.15 — the end of the stable part: $D=\max(0,\min(D_L,D_R+1))$
-- statement:
--   With $i_0$, $k$, $L=\ell_{i_0}$, $R=r_{i_0}$ and the phrase $P\ni i_0$ as in §5 ($R\in[k..1.5k)$, $k\in\mathbb K$, $L\le1.5k$), let
--   $$D=\max\big(0,\min(D_L,D_R+1)\big).$$
--   Then for every $x\in[0..D]$ the r-value of $sJ^x(i_0)$ is at least $k$. Furthermore $j=sJ^{D+1}(i_0)$ is well defined and satisfies one of: (1) $r_j<k$; (2) $j^*=sJ(j)$ is well defined and $r_{j^*}<k$.
--
--   The lemma identifies, from two path sums in $T_{\mathrm{bad}}$, the step at which the stable part ends; Lemma 3.2 computes it with level-ancestor queries.
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - encoding: K = {1.5^i | i ∈ [0..log_{1.5}(n/z)]} → Klev n z = {(3/2)^e | e ∈ ℕ, (3/2)^e ≤ n/z} ⊆ ℝ; reason: i ≤ log_{1.5}(n/z) iff 1.5^i ≤ n/z; the elements stay real numbers and [k..1.5k) is the set of integers in [k, 1.5k)
--   - reading: §5's fixed input i0 (r_{i0} = R ∈ [k..1.5k), k ∈ K, ℓ_{i0} = L ≤ 1.5k) → hypotheses on i₀ and k in the statement; reason: standing assumption of §5 (p. 24, p. 30) and the hypothesis of Lemma 3.2
--   - reading: D_L, D_R the maximal integers with ΔL(D_L) ≤ L, ΔR(D_R) ≤ R − k → maxima over D ∈ [−1..depth(P) − 1]; reason: ΔL(P, D) and ΔR(P, D) are defined in the paper exactly on this range (the depth-th ancestor is a root with undefined δℓ, δr); ΔL(−1) = ΔR(−1) = 0 makes the maxima exist
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 30, Lemma 5.15

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd
import Definitions.Def_LZEndAccess_Main_StablePart

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Lemma 5.15** (p. 30). With `i₀`, `k`, `L = ℓ_{i₀}`, `R = r_{i₀}` and `P` as in §5, let
`D = max(0, min(D_L, D_R + 1))`. For every `x ∈ [0..D]` the r-value of `sJ^x(i₀)` is at least
`k`; moreover `j = sJ^{D+1}(i₀)` is well defined and either `r_j < k`, or `j* = sJ(j)` is well
defined and `r_{j*} < k`. -/
theorem lemma_5_15 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (k : ℝ) (hk : k ∈ Klev S.length Z.length) (i₀ : ℕ) (hi : 1 ≤ i₀) (hin : i₀ ≤ S.length)
    (hR1 : k ≤ (rVal Z i₀ : ℝ)) (hR2 : (rVal Z i₀ : ℝ) < 3 / 2 * k)
    (hL : (lVal Z i₀ : ℝ) ≤ 3 / 2 * k)
    (t : ℕ) (ht : InPhrase Z t i₀) :
    (∀ x : ℕ, (x : ℤ) ≤ max 0 (min (DL Z t (lVal Z i₀)) (DR Z t (rVal Z i₀) k + 1)) →
      ∃ j, sJiter Z x i₀ = some j ∧ k ≤ (rVal Z j : ℝ)) ∧
    ∃ j, sJiter Z ((max 0 (min (DL Z t (lVal Z i₀)) (DR Z t (rVal Z i₀) k + 1))).toNat + 1) i₀
        = some j ∧
      ((rVal Z j : ℝ) < k ∨ ∃ j', sJ Z j = some j' ∧ (rVal Z j' : ℝ) < k) := by sorry

end LZEndAccess.Main
