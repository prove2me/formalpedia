-- Prove2me | Theorems.Thm_KServer_chunk_regrid
-- name    : KServer.chunk_regrid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T14:13:12.612761+00:00
-- url     : https://prove2.me/theorems/22e6eceb-34e3-4735-907e-39e5a714c583
-- title:
--   Grid regrouping of chunk systems with variance control
-- statement:
--   **Grid regrouping of chunk systems, with exact totals and variance control.** Let \(C\) be a chunk system with online escapes on a metric space \(X\) with marked points \(s, t\): a finite probability space of outcomes carrying a filtration, whose request sequence is split into \(m\) adapted chunks with conditional sizes \(c_i(\omega) \in [c_A, c_B]\), each certified against all evaders and online bail rules at escape price \(p_e\), with offline cost at most \(d(s,t)\) and expected total size at least \(T\). Fix a spacing \(\delta > 0\) with \(c_B \le 2\delta\), a window count \(M \le m\) large enough that the total size is pointwise at most \(2\delta M\), and suppose the time-zero history is trivial and the total size has variance at most \(V\): $$\sum_\omega P(\omega)\Big(\sum_i c_i(\omega) - \mathbb{E}\big[\textstyle\sum_i c_i\big]\Big)^2 \le V.$$ Then the chunks can be regrouped along the hitting times of the cumulative-mass grid \(\{2\delta j\}_{j \le M}\) into a chunk system with the same request sequence and \(M\) chunks whose sizes lie pointwise in \([0, 2\delta + c_B]\), at escape price \(p' \ge p_e + 2\delta + c_B\), such that the expected total is preserved exactly, the new time-zero history is again trivial, and the new total size has variance at most $$V' \;\ge\; \tfrac54\, V + 20\,(2\delta + c_B)\,\mathbb{E}\big[\textstyle\sum_i c_i\big].$$ The variance bound comes from the orthogonal-increment decomposition of the output total: the output sizes are conditional expectations of the grid-window masses at their starting times, so the centred output total is a sum of martingale differences combining the Doob increments of the input total with window-restricted increments of the individual window masses; the former contribute the input variance, the latter a ceiling-scale term. This is the load-bearing renormalization step of the Bienkowski-Coester-Rabinovich lower-bound induction: it re-spaces chunk sizes to the next scale while carrying the variance invariant needed at the following level, with no loss in the expected total.
-- source:
--   BCR randomized k-server lower bound, combining/renormalization layer (v3)

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_chunk_saturate
import Definitions.Def_KServer_chunk_var

namespace KServer

theorem chunk_regrid {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ p' V V' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hcB2δ : cB ≤ 2 * δ) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hTmax : ∀ ω, (∑ i, C.size ω i) ≤ 2 * δ * M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hV' : 5 / 4 * V
      + 20 * ((2 * δ + cB) * ∑ ω, C.P ω * ∑ i, C.size ω i) ≤ V') :
    ∃ C' : ChunkSystemB X s t 0 (2 * δ + cB) T p' M,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V') := by sorry

end KServer
