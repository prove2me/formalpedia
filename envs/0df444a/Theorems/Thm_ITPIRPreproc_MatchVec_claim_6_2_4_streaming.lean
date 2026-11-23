-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_4_streaming
-- name    : ITPIRPreproc.MatchVec.claim_6_2_4_streaming
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:38.536318+00:00
-- url     : https://prove2.me/theorems/997bde65-fe40-4104-9d8a-fcd3dccc0fbb
-- title:
--   Claim 6.2.4 (streaming hint computation)
-- statement:
--   This is the streaming half of Claim 6.2.4. Let $m=2^h$, $h\ge3$, and $d=\dim(h)$, and let an implementation already satisfy the non-streaming claims. There are deterministic initialization and per-chunk word-RAM programs which, for every $L\ge E=m/8$ and every input list of $L$ keys, process the database in $E$ consecutive chunks and finish with the encoded list of all $L$ hints. Initialization work, work per chunk and total storage are at most $L\,t_{\rm stream}$ with $t_{\rm stream}(n)=d\,\mathrm{poly}(h)$, including keys, the public vector table and workspace. Installing these programs into the implementation yields the complete §4.1 efficiency structure with the original basic, Query, Decode and Answer bounds.
--
--   **Formalization Note** The programs must work for every implementation satisfying the explicit non-streaming interface; this ensures that the parent uses the same codes and non-streaming programs for both halves. `withStreams` changes only the two streaming fields.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Claim 6.2.4 and its proof, printed p.23 (PDF p.25), streaming paragraph; streaming algorithm printed p.21 (PDF p.23)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
import Definitions.Def_ITPIRPreproc_MatchVec_OfflineEfficiency

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- Claim 6.2.4, streaming part: for every implementation satisfying the common non-streaming
interface, there are deterministic initialization and per-chunk programs implementing (14)'s
hint for every list of at least E keys. Installing them leaves all other components unchanged
and yields the full §4.1 efficiency structure. -/
theorem claim_6_2_4_streaming :
    ∀ (C₀ : ℝ) (c₀ : ℕ) (C : ℝ) (c : ℕ),
      activationCostFloor C₀ ≤ C → activationExponentFloor c₀ ≤ c →
      ∀ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
        (vecProg tableProg : Program) (I : OCHPImpl (actFamily dim u v)),
        (∀ h : ℕ, 3 ≤ h → IsMVFamily (2 ^ h) (dim h) (u h) (v h)) →
        MVComputable dim u v C₀ c₀ vecProg tableProg →
        (∀ h : ℕ, 3 ≤ h →
          I.NonStreamEfficient (2 ^ h) (C * h * dim h) (C * dim h * (h : ℝ) ^ c)
            (C * h * dim h) (C * h * dim h) (C * 2 ^ h * dim h * (h : ℝ) ^ c)
            ((h + 1) * dim h) (2 * dim h)) →
        ∃ (si sc : Program),
          Deterministic si ∧ Deterministic sc ∧
          ∀ h : ℕ, 3 ≤ h →
            (I.withStreams si sc).Efficient (2 ^ h) (C * h * dim h)
              (C * dim h * (h : ℝ) ^ c) (C * h * dim h) (C * h * dim h)
              (C * 2 ^ h * dim h * (h : ℝ) ^ c) ((h + 1) * dim h) (2 * dim h) := by sorry
