-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_lemma_A_1
-- name    : MaxCutSample2027.Coreset.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:51:14.477361+00:00
-- url     : https://prove2.me/theorems/804dcb2f-79db-4ed2-97a4-8336010298b3
-- title:
--   Lemma A.1 — absolute-value Rademacher contraction
-- statement:
--   Let $k\ge1$, let $T\subseteq\mathbb R^k$ be nonempty and compact, and let $g:\mathbb R\to\mathbb R$ be 1-Lipschitz with $g(0)=0$. For independent uniform signs $\sigma_0,\ldots,\sigma_{k-1}\in\{-1,1\}$,
--   $$\mathbb E_\sigma\max_{t\in T}\left|\frac1k\sum_{i=0}^{k-1}\sigma_i g(t_i)\right|\le
--   2\mathbb E_\sigma\max_{t\in T}\left|\frac1k\sum_{i=0}^{k-1}\sigma_i t_i\right|.$$
--   This is the contraction estimate for a fixed class of vectors. It retains both absolute values and the exact factor two.
--
--   **Formalization Note** Sign expectations are the uniform finite average. Compactness of T and Lipschitz continuity of g ensure that the real suprema encode attained maxima.
--
--   Differences from the source:
--   - encoding: independent uniform signs and maxima over compact T → Boolean sign vectors on Fin k, the uniform finite average, and compact-image real suprema; reason: all sign assignments are retained and Lipschitz continuity makes every supremum finite and attained
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma A.1, p. 33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_signed
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem lemma_A_1 (k : ℕ) (hk : 1 ≤ k)
    (T : Set (Fin k → ℝ)) (hT : T.Nonempty) (hcompact : IsCompact T)
    (g : ℝ → ℝ) (hg : LipschitzWith 1 g) (hg0 : g 0 = 0) :
    signAverage k (contractionMaximum T g) ≤
      2 * signAverage k (contractionMaximum T (fun t => t)) := by sorry

end MaxCutSample2027.Coreset
