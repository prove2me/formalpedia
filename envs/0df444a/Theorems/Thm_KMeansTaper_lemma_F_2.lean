-- Prove2me | Theorems.Thm_KMeansTaper_lemma_F_2
-- name    : KMeansTaper.lemma_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:43.35484+00:00
-- url     : https://prove2.me/theorems/bf1ca3d6-4fdf-4056-a351-c48462199347
-- title:
--   Lemma F.2 — sparsification
-- statement:
--   Let $I$ be an instance, $t\ge1$ an integer, and $\mathrm{OPT}\subseteq F$ an optimal set with exactly $k$ facilities, $\mathrm{opt}=\mathrm{cost}_2(\mathrm{OPT})=\mathrm{OPT}_k$. Consider the restricted facility sets $F'$ obtained by deleting the facility balls $\mathrm{FBall}(i_x,d(i_x,i'_x))$, $x\le q$, for all sequences of $q\le t$ facility pairs $(i_x,i'_x)$. Then
--
--   1. there are at most $n^{2t+2}$ such sets, where $n=|J|+|F|$;
--   2. at least one of them satisfies $\mathrm{OPT}\subseteq F'$, hence $\mathrm{opt}_{I'}=\mathrm{opt}$, and every facility of $F'$ is $\mathrm{opt}/t$-sparse.
--
--   Sparsification lets the reduction of Theorem F.1 assume that no facility carries a large share of the optimum near it.
--
--   Differences from the source:
--   - generalization: t = ⌈14400αc/ε⌉ (proof of Theorem F.1) → every integer t ≥ 1; reason: the lemma's proof works for every t ≥ 1 and specializes to the paper's t
--   - generalization: density defined for A > 0 (so opt > 0) → opt ≥ 0, A = opt/t; reason: for opt = 0 no facility is 0-dense; the case opt > 0 is the paper's
--   - encoding: at most n^{2t+2} instances → the finite set of distinct F' has at most (|J| + |F|)^{2t+2} elements; reason: a restricted instance is determined by F'
--   - encoding: OPT a fixed optimal set with exactly k facilities → hypotheses OPT ⊆ F, |OPT| = k, cost2 OPT = OPT_k; reason: same object
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Lemma F.2, p.43 (PDF p.46), with the Notation of p.42 (PDF p.45)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2
import Definitions.Def_KMeansTaper_IsDense

namespace KMeansTaper

open OAI.MetricKMedian (Instance)

/-- **Lemma F.2 (sparsification)**, p.43 (PDF p.46), with the notation of p.42 (PDF p.45).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Let `OPT` be an optimal set with exactly `k` facilities and `opt = cost(OPT)`. Among the
restricted instances obtained by deleting the facility balls `FBall(i_x, d(i_x, i'_x))`,
`x ≤ q`, for all sequences of `q ≤ t` facility pairs (at most `n^{2t+2}` instances,
`n = |J| + |F|`), at least one satisfies `OPT ⊆ F'` (so `opt_{I'} = opt_I`) and every facility
of `F'` is `opt/t`-sparse.

**Formalization Note.** Stated for every integer `t ≥ 1` (the proof of Theorem F.1 uses
`t = ⌈14400αc/ε⌉`), including `opt = 0`. `n` is `|J| + |F|` as on p.43. -/
theorem lemma_F_2 (I : Instance) (t : ℕ) (ht : 1 ≤ t) (OPT : Finset (Fin I.n))
    (hOPT : OPT ⊆ I.facilities) (hcard : OPT.card = I.k) (hopt : cost2 I OPT = optimum2 I) :
    (sparsifyFamily I t).card ≤ (I.clients.card + I.facilities.card) ^ (2 * t + 2) ∧
    ∃ F' ∈ sparsifyFamily I t, OPT ⊆ F' ∧ optimumOn I F' = optimum2 I ∧
      ∀ i ∈ F', ¬ IsDense I OPT (optimum2 I / t) i := by sorry

end KMeansTaper
