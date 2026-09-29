-- Prove2me | Theorems.Thm_KServer_chunk_regroup
-- name    : KServer.chunk_regroup
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T12:39:17.682545+00:00
-- url     : https://prove2.me/theorems/ba6d0d18-de5e-4b20-90e7-66ed3b96928d
-- title:
--   Chunk regrouping with mass caps and variance-controlled loss
-- statement:
--   **The chunk-regrouping lemma** (the load-bearing repair of Lemma 15 of Bubeck–Coester–Rabani, STOC 2023). Let \(C\) be a chunk system with online escapes on a metric space \(X\) with marked points \(s, t\): sizes in \([c_A, c_B]\) with \(0 \le c_A \le c_B\), escape price \(p_e \ge 0\), expected total mass \(T_0 = \sum_\omega P(\omega) \sum_i c_i(\omega) > 0\), and total-mass variance \(\mathrm{Var} = \sum_\omega P(\omega)(\sum_i c_i(\omega) - T_0)^2 \le V\). Fix a spacing \(\delta > 0\) and a generous window count \(M\) with \(2T_0 + 4\delta \le (M-1)\delta\) and \(M \le \tilde m\). Then the chunks regroup into exactly \(M\) windows — delimited by the hitting times of the absolute levels \(T_0 - k\delta\) of the conditional future mass, ended early once a window has accumulated mass \(2\delta\), forced nonempty, and capped so that the windows partition the sequence exactly — giving a chunk system
--
--   $$C' : \mathrm{ChunkSystemB}(X, s, t,\ 0,\ 2\delta + c_B,\ T',\ p',\ M)$$
--
--   serving the identical request sequence, with pointwise sizes at most \(2\delta + c_B\), for any escape price \(p' \ge p_e + 2\delta + c_B\), and any total \(T' \le T_0 - 2V/T_0\). Unlike the original combining lemma, NO bound on the jumps of the conditional-expectation process and no monotonicity are assumed: the escape charging is financed pointwise by the mass caps; the loss of expected total is confined to the effective truncation of the final forced window, and a counting argument (down-crossings are at most \(T_0/\delta\); every other non-capped window consumes mass \(2\delta\); a bound cap chains to exact exhaustion) shows the truncation can only occur on outcomes whose total is at least \(2T_0\), so Chebyshev bounds the expected loss by \(2V/T_0\). The conditional window sizes are exact optional-stopping telescopes, so the premise and the adapted filtration (hitting time paired with the fine history) transfer verbatim. This is the form of the combining step that survives the recursion of the BCR induction, where sharp per-level control of conditional-expectation jumps is impossible.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 15, repaired robust form.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_chunk_saturate

namespace KServer

theorem chunk_regroup {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ V T' p' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hT0 : 0 < ∑ ω, C.P ω * ∑ i, C.size ω i)
    (hM1 : 2 * (∑ ω, C.P ω * ∑ i, C.size ω i) + 4 * δ ≤ (M - 1 : ℕ) * δ)
    (hVar : ∑ ω, C.P ω *
      ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hT' : T' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i)
      - 2 * V / (∑ ω, C.P ω * ∑ i, C.size ω i)) :
    Nonempty (ChunkSystemB X s t 0 (2 * δ + cB) T' p' M) := by sorry

end KServer
