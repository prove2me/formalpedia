-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_4_2
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:04:36.893501+00:00
-- url     : https://prove2.me/theorems/783b38ee-3dc0-4e2d-b16f-f5456597b16f
-- title:
--   Lemma 4.2 — imbalance among three sample counts
-- statement:
--   Let $k\ge512$ be an integer. Draw $k$ independent uniform labels from $\{0,1,2\}$, let $N_j$ be the number of occurrences of label $j$, and set $M=\max_jN_j$ and $L=M-k/3$. Equivalently, the count vector has distribution $\operatorname{Multinomial}(k;1/3,1/3,1/3)$. Then
--   $$\Pr\left(\frac{\sqrt k}{12}<L\le\frac k6\right)>\frac38.$$
--   The strict lower threshold and strict probability bound are part of the claim. This is the imbalance estimate for the tripartite lower-bound graph.
--
--   Differences from the source:
--   - encoding: the probability of a sample event under independent draws with replacement → the finite product-law average of its indicator over Fin k sample positions; reason: each ordered sample has exactly its source probability, and the event retains the source strict or non-strict inequalities
--   - encoding: Multinomial(k; 1/3, 1/3, 1/3) counts → counts of k independent uniform Fin 3 labels; reason: the resulting count vector has exactly that multinomial law
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 4.2, p. 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_4_2 (k : ℕ) (hk : 512 ≤ k) :
    (3 : ℝ) / 8 < eventProbability (uniformLaw (V := Fin 3)) k
      (fun ω => Real.sqrt (k : ℝ) / 12 < imbalance ω ∧ imbalance ω ≤ (k : ℝ) / 6) := by sorry

end MaxCutSample2027.Coreset.Supplement
