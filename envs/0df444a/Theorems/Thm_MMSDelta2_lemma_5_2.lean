-- Prove2me | Theorems.Thm_MMSDelta2_lemma_5_2
-- name    : MMSDelta2.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:39.771315+00:00
-- url     : https://prove2.me/theorems/6a60209c-952e-47c0-8bbc-16ce7ab41921
-- title:
--   Lemma 5.2 — rigidity of the KPW core: value-one partitions are rows or columns
-- statement:
--   If $(X_1,\dots,X_5)$ is a partition of $M^+$ such that
--
--   $$\sum_{(i,j)\in X_t}M_{i,j}=1\qquad\text{for every }t\in[5],$$
--
--   then $(X_1,\dots,X_5)$ is either the row partition or the column partition, up to relabeling.
--
--   This is the rigidity property of the core that every hardness reduction of the paper relies on.
--
--   Differences from the source:
--   - encoding: a partition (X₁, …, X₅) of M⁺; 'up to relabeling' → an indexed family of pairwise disjoint sets with union M⁺; X_t = R_{π t} (or C_{π t}) for a permutation π; reason: same statement
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 5.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MMSDelta2_KPW

namespace MMSDelta2

/-- **Lemma 5.2**, p.18 (PDF p.20).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

If `(X_1, …, X_5)` is a partition of `M⁺` with `Σ_{(i,j)∈X_t} M_{i,j} = 1` for every `t ∈ [5]`,
then `(X_1, …, X_5)` is the row partition or the column partition, up to relabeling.

**Formalization Note.** Partitions are indexed families of pairwise disjoint sets with union `M⁺`;
"up to relabeling" is a permutation of the bundle indices (`IsRowOrColPartition`). -/
theorem lemma_5_2 (X : Fin 5 → Finset (Fin 5 × Fin 5)) (hX : IsPartitionOf kpwMplus X)
    (hsum : ∀ t, kpwMsum (X t) = 1) : IsRowOrColPartition kpwMplus X := by sorry

end MMSDelta2
