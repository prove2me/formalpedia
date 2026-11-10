-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_lemma_3_2
-- name    : GreedyColoringLCA969.LowerBound.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:43:15.9654+00:00
-- url     : https://prove2.me/theorems/2c959a29-b845-4843-af94-fbcaa71a6704
-- title:
--   Lemma 3.2 — high girth and a large high-color fraction
-- statement:
--   For every real $\varepsilon>0$, there are constants $C,C'>0$ such that for all real thresholds $\Delta,g>C'$ there exists a nonempty finite simple graph $G$ on $n$ vertices, with maximum degree at most $\Delta$ and girth at least $g$, for which every proper positive-integer coloring $c$ satisfies
--
--   $$\left|\left\{v:c(v)\ge\frac{C\Delta}{\log_2\Delta}\right\}\right|\ge(1-\varepsilon)n.$$
--
--   The constants precede both thresholds, the graph, and its coloring. This supplies the bounded-degree, high-girth graphs used by the lower bound, retaining the high-color fraction rather than only a chromatic-number lower bound.
--
--   **Formalization Note** The threshold $C'$ is chosen greater than one and the witness is explicitly nonempty, as in Appendix A.1. Forests have no short cycles and hence infinite girth in the source convention.
--
--   Differences from the source:
--   - encoding: vertex identifiers [n] and positive integer colors → Fin n with zero-based identifiers and positive-integer color type; reason: adding one is a bijection on vertex identifiers; colors remain exactly positive integers
--   - reading: untyped degree and girth thresholds Delta and g → real Delta and g, with integer degrees and cycle lengths coerced to real numbers; reason: this is the inclusive reading; in particular every integer-threshold instance is retained
--   - encoding: existential positive threshold and the nonempty graph constructed in Appendix A.1 → C prime greater than one and an explicitly nonempty witness; reason: the existential threshold can always be enlarged; the construction has positive size and the logarithm is positive
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Lemma 3.2, p.11 (PDF 12); proof pp.35–36 (PDF 36–37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Lemma 3.2, printed p.11 / PDF 12, proved in Appendix A.1.
Real degree and girth thresholds retain the inclusive reading of the untyped source.
The finite witness is nonempty, as in the construction; thresholds may exceed one. -/
theorem lemma_3_2 (ε : ℝ) (hε : 0 < ε) :
    ∃ C C' : ℝ, 0 < C ∧ 1 < C' ∧
      ∀ Δ g : ℝ, C' < Δ → C' < g →
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n ∧
          MaxDegreeAtMost G Δ ∧ GirthAtLeast G g ∧
          ∀ c : Fin n → ℕ+, IsProper G c →
            (1 - ε) * (n : ℝ) ≤
              (Nat.card {v : Fin n // C * Δ / log2 Δ ≤ ((c v).val : ℝ)} : ℝ) := by sorry

end GreedyColoringLCA969.LowerBound
