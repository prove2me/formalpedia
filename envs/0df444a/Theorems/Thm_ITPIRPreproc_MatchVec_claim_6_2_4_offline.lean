-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_4_offline
-- name    : ITPIRPreproc.MatchVec.claim_6_2_4_offline
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:30.131528+00:00
-- url     : https://prove2.me/theorems/2be1190e-0305-49b5-a7fd-15616fa9ccfa
-- title:
--   Claim 6.2.4 (non-streaming programs and codes)
-- statement:
--   This is the non-streaming half of Claim 6.2.4, for one matching-vector family computable with constants $(C_0,c_0)$. It asks for a single implementation with injective $(h+1)d$-bit key codes and $2d$-bit hint and answer codes, and with the following worst-case bounds: both samplers and the compatibility test take $O(hd)$ work; Query and Decode take $O(hd)$; Answer and the one-shot Hint program take $md\,\mathrm{poly}(h)$. The public table is the matching-vector table supplied by `MVComputable`, and all input-processing requirements of §4.1 are included. The selected constants are at least the common floors $2^{32}(|C_0|+1)$ and $c_0+32$, allowing the same implementation to be used by the streaming half.
--
--   **Formalization Note** `NonStreamEfficient` is precisely `OCHPImpl.Efficient` with its two streaming fields omitted. Nothing about the streaming programs is asserted here.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Claim 6.2.4, printed p.23 (PDF p.25), first four sentences; efficiency interface §4.1, printed p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
import Definitions.Def_ITPIRPreproc_MatchVec_OfflineEfficiency

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- Claim 6.2.4, non-streaming part: one implementation supplies the exact codes, the public
matching-vector table, both samplers, the compatibility test, Query, Answer, Decode and the
one-shot Hint program with the stated cost bounds. -/
theorem claim_6_2_4_offline :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ (C : ℝ) (c : ℕ),
      activationCostFloor C₀ ≤ C ∧ activationExponentFloor c₀ ≤ c ∧
      ∀ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
        (vecProg tableProg : Program),
        (∀ h : ℕ, 3 ≤ h → IsMVFamily (2 ^ h) (dim h) (u h) (v h)) →
        MVComputable dim u v C₀ c₀ vecProg tableProg →
        ∃ (I : OCHPImpl (actFamily dim u v)) (hintProg : Program),
          Deterministic hintProg ∧
          ∀ h : ℕ, 3 ≤ h →
            (Function.Injective (I.encKey (2 ^ h)) ∧
              ∀ K, (I.encKey (2 ^ h) K).length = (h + 1) * dim h) ∧
            (Function.Injective (I.encHint (2 ^ h)) ∧
              ∀ z, (I.encHint (2 ^ h) z).length = 2 * dim h) ∧
            (Function.Injective (I.encAns (2 ^ h)) ∧
              ∀ a, (I.encAns (2 ^ h) a).length = 2 * dim h) ∧
            I.NonStreamEfficient (2 ^ h) (C * h * dim h) (C * dim h * (h : ℝ) ^ c)
              (C * h * dim h) (C * h * dim h) (C * 2 ^ h * dim h * (h : ℝ) ^ c)
              ((h + 1) * dim h) (2 * dim h) ∧
            ∀ (D : Fin (2 ^ h * 2 ^ h) → Bool) (K : (actFamily dim u v (2 ^ h)).Key),
              let inp := encNat (2 ^ h) ++ encBits (I.encKey (2 ^ h) K) ++ List.ofFn D
              Halts hintProg inp zeroTape ∧
              output hintProg inp zeroTape =
                I.encHint (2 ^ h) ((actFamily dim u v (2 ^ h)).hint D K) ∧
              (cost hintProg inp zeroTape : ℝ) ≤ C * 2 ^ h * dim h * (h : ℝ) ^ c := by sorry
