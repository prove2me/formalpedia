-- Prove2me | Theorems.Thm_ModFormPIR_theorem_9_4
-- name    : ModFormPIR.theorem_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:55.309066+00:00
-- url     : https://prove2.me/theorems/a6b53c95-6b23-4dda-b389-ae1269ee5c6d
-- title:
--   Theorem 9.4 ([DPT10]), p.35 — a dictionary with redundancy $O(N/\sqrt K)$
-- statement:
--   There is an absolute constant $c>0$ such that for all integers $K,N\ge2$ there exist an integer $L\le\lceil N\log_2K+cN/\sqrt K\rceil$ and deterministic algorithms $\mathrm{Encode}_{K,N}:[K]^N\to\{0,1\}^L$ and $\mathrm{Decode}_{K,N}:[N]\times\{0,1\}^L\to[K]$ such that:
--
--   1. $\mathrm{Decode}_{K,N}(i,\mathrm{Encode}_{K,N}(v))=v_i$ for all $v$, $i$;
--   2. given random access to the encoded string, $\mathrm{Decode}_{K,N}$ uses $\mathrm{poly}(\log N,\log K)$ bit operations;
--   3. $\mathrm{Encode}_{K,N}$ uses $N\cdot\mathrm{poly}(\log N,\log K)$ bit operations.
--
--   The paper stores tables of $\mathbb F_p$-elements through this dictionary, which, with $p$ just above a power of two, is what brings storage to $n+1$ bits.
--
--   **Formalization Note** This is a cited result, stated as the paper prints it. Random access to the code is `probe`, and symbols sit one bit per cell.
--
--   Differences from the source:
--   - reading: "bit operations" → machine steps with symbols one bit per cell; reason: the source names no machine; each step then touches O(1) symbol bits, and words carry addresses
--   - reading: algorithms Encode_{K,N}, Decode_{K,N} for each K, N → one program pair for all K, N, with K as input; reason: Lemma 9.6 runs them for a p chosen at run time
--   - encoding: poly(log N, log K) → C·(⌊log₂ N⌋ + ⌊log₂ K⌋ + 2)^e; reason: the meaning of poly
--   - encoding: bit model without word size → W ≥ b(⌊log₂ N⌋ + ⌊log₂(⌊log₂ K⌋+1)⌋ + 1); reason: a word must address the L ≈ N log₂ K bits of the code
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Theorem 9.4, p.35 (PDF p.39), citing Dodis, Pătraşcu, Thorup, Changing base without losing space, STOC 2010

import Mathlib
import Definitions.Def_ModFormPIR_Layouts

set_option autoImplicit false

namespace ModFormPIR

/-- **Theorem 9.4** ([DPT10]), p.35. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
There is an absolute `c > 0` such that for all `K, N ≥ 2` there is `L ≤ ⌈N log₂ K + cN/√K⌉`, an encoder `[K]^N → {0,1}^L` in `N · poly(log N, log K)`
bit operations, and a decoder that recovers any `v_i` from random access to the code in `poly(log N, log K)` bit operations.

**Formalization Note.** "Bit operations" are read as machine steps, with symbols one bit per cell, so each step handles
`O(1)` bits of a symbol and a word only holds an address; random access is `probe`. The word must address `L ≈ N log₂ K` bits, hence
`W ≥ b(log₂ N + log₂(log₂ K + 1) + 1)`. One program pair serves all `K, N`. `L` is a function of `K, N`, `N` positions are `Fin N`, and `[K]` is
`{0, …, K-1}`, the symbols being given as naturals below `K`. -/
theorem theorem_9_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ (L : ℕ → ℕ → ℕ) (enc dec : Program) (b C e : ℕ),
      NoProbe enc ∧ NoCoin enc ∧ NoCoin dec ∧
      ∀ K N : ℕ, 2 ≤ K → 2 ≤ N →
        ((L K N : ℤ) ≤ ⌈(N : ℝ) * Real.logb 2 K + c * N / Real.sqrt K⌉) ∧
        ∀ W ≥ b * (Nat.log2 N + Nat.log2 (Nat.log2 K + 1) + 1),
        ∀ v : Fin N → ℕ, (∀ i, v i < K) →
          ∃ code : List Bool, code.length = L K N ∧
            (∃ (t : ℕ) (st : State W), t ≤ C * N * (Nat.log2 N + Nat.log2 K + 2) ^ e ∧
              Accepts enc [] zeroTape (dictEncInput K v) t st ∧
              BitCellsOK st (-1) (L K N) ∧ code = readBits st (-1) (L K N)) ∧
            ∀ i : Fin N, ∃ (t : ℕ) (st : State W), t ≤ C * (Nat.log2 N + Nat.log2 K + 2) ^ e ∧
              Accepts dec code zeroTape (dictDecInput N K i) t st ∧
              BitCellsOK st (-1) K.size ∧ readNat st (-1) K.size = v i := by sorry

end ModFormPIR
