-- Prove2me | Theorems.Thm_KMeansTaper_lemma_F_3
-- name    : KMeansTaper.lemma_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:14.675437+00:00
-- url     : https://prove2.me/theorems/30e3518a-4750-4103-bed2-3e04fdb51596
-- title:
--   Lemma F.3 — the algorithm on a sparse instance
-- statement:
--   Let $I$ be an instance with an optimal set $\mathrm{OPT}$ of exactly $k$ facilities, $\mathrm{opt}=\mathrm{OPT}_k$, and let $F'$ with $\mathrm{OPT}\subseteq F'\subseteq F$ be such that every facility of $F'$ is $A$-sparse, $A\ge0$. Let $T\subseteq F'$ with $|T|\le k+c$, let $t\ge7200c$ and
--
--   $$\Gamma^*=2\cdot3600\Bigl(A+\frac{\mathrm{cost}_2(T)}{t}\Bigr).$$
--
--   Then the algorithm on a sparse instance, run with $\Gamma=\Gamma^*$, has an output, and every output $S$ satisfies $S\subseteq F'$, $|S|\le k$ and
--
--   $$\mathrm{cost}_2(S)\le\max\Bigl\{\mathrm{cost}_2(T)+c\,\Gamma^*,\ \tfrac{169}{49}\,\mathrm{opt}\Bigr\}.$$
--
--   This removes the $c$ extra facilities of an additive approximation on a sparse instance.
--
--   **Formalization Note** For $t=0$ (possible only when $c=0$, where step (3) is never reached) Lean reads $\mathrm{cost}_2(T)/0=0$.
--
--   Differences from the source:
--   - generalization: I′ A-sparse with A > 0 (Notation, p.42) → A ≥ 0; reason: the proof uses only A ≥ 0; the paper's A > 0 is a special case
--   - generalization: the output S satisfies … → an output exists, and every output (every tie-break) satisfies …; reason: Lean also asserts that the algorithm returns a set
--   - encoding: the output is a set of facilities of I′ → S ⊆ F′ stated in the conclusion; reason: the algorithm returns subsets of F′
--   - encoding: cost(T)/t with t ≥ 7200c → cost2 I T / t with t : ℕ (0 when t = 0); reason: t = 0 forces c = 0, where Γ* is not used
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Lemma F.3, p.43 (PDF p.46), with "Algorithm on a sparse instance", p.43

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2
import Definitions.Def_KMeansTaper_IsDense
import Definitions.Def_KMeansTaper_IsSparseOutput

namespace KMeansTaper

open OAI.MetricKMedian (Instance)

/-- **Lemma F.3 (sparse instance)**, p.43 (PDF p.46), for the algorithm on a sparse instance of
p.43.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Let `I'` be the restriction to `F'`, `A`-sparse, with `OPT ⊆ F'`, `T ⊆ F'`, `|T| ≤ k + c`,
`t ≥ 7200c` and `Γ = Γ* := 2 · 3600 (A + cost(T)/t)`. Then the output `S` satisfies
`|S| ≤ k` and `cost(S) ≤ max{cost(T) + cΓ*, (169/49) opt}`.

**Formalization Note.** `OPT` is an optimal set of `I` with exactly `k` facilities. The
output is the relation `IsSparseOutput` (every tie-break of the minimizers and of the cheapest
pair); the first conjunct says an output exists. `A ≥ 0` (the notation of p.42 has `A > 0`).
For `t = 0` (only possible when `c = 0`) Lean reads `cost(T)/0 = 0`. -/
theorem lemma_F_3 (I : Instance) (OPT F' : Finset (Fin I.n)) (hOPT : OPT ⊆ F')
    (hF' : F' ⊆ I.facilities) (hcard : OPT.card = I.k) (hopt : cost2 I OPT = optimum2 I)
    (A : ℝ) (hA : 0 ≤ A) (hsparse : ∀ i ∈ F', ¬ IsDense I OPT A i)
    (T : Finset (Fin I.n)) (hT : T ⊆ F') (c t : ℕ) (hTc : T.card ≤ I.k + c)
    (ht : 7200 * c ≤ t) :
    (∃ S, IsSparseOutput I F' T (2 * 3600 * (A + cost2 I T / t)) t S) ∧
    ∀ S, IsSparseOutput I F' T (2 * 3600 * (A + cost2 I T / t)) t S →
      S ⊆ F' ∧ S.card ≤ I.k ∧
      cost2 I S ≤ max (cost2 I T + c * (2 * 3600 * (A + cost2 I T / t)))
        (169 / 49 * optimum2 I) := by sorry

end KMeansTaper
