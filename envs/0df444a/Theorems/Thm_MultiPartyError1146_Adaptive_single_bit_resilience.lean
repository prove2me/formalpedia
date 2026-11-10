-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_single_bit_resilience
-- name    : MultiPartyError1146.Adaptive.single_bit_resilience
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:25.884858+00:00
-- url     : https://prove2.me/theorems/08e8d7cf-e0e5-4f6e-92c1-98197be30797
-- title:
--   Lemma 4.2 — single-bit resilience and rate
-- statement:
--   For every $\eta>0$ there are positive constants $c\le1$ and $K$, independent of all sizes, inputs and noise, such that every $n\ge1$ has a deterministic causal CAS protocol for one-bit dissemination with
--   $$\delta=c/\sqrt n,\qquad T\le K n^{3/2+\eta}\log(2n).$$
--   Every party within the factor-10 local budget recovers all inputs. The external parameter $\eta$ is arbitrary, even though the witness chooses an internal reciprocal-integer parameter. All small sizes remain included.
--
--   Differences from the source:
--   - encoding: Ωη(1/√n) resilience and tilde-Ωη(n^(−1/2−η)) rate → uniform cη,Kη>0 for all positive n, resilience cη/√n and duration at most Kη n^(3/2+η) log(2n), with one-bit inputs; reason: the proof has one logarithmic loss; log(2n) and uniform constant adjustment retain every small size
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 4.2, printed p.20, PDF p.22

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Protocol

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem single_bit_resilience :
    ∀ η : ℝ, 0 < η → ∃ c K : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < K ∧
      ∀ n : ℕ, 1 ≤ n → ∃ T : ℕ, 1 ≤ T ∧ ∃ P : Protocol n 1 T,
        Resilient P (c / Real.sqrt n) ∧
          (T : ℝ) ≤ K * (n : ℝ) ^ ((3 : ℝ) / 2 + η) * Real.log (2 * n) := by sorry

end MultiPartyError1146.Adaptive
