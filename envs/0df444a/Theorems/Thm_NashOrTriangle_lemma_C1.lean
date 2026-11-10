-- Prove2me | Theorems.Thm_NashOrTriangle_lemma_C1
-- name    : NashOrTriangle.lemma_C1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:50:56.953071+00:00
-- url     : https://prove2.me/theorems/28e82417-cd89-4ff9-bc18-88706c75a91f
-- title:
--   Lemma C.1 (Assos et al.) — gap-$h$ pair within $2^{O(s^2dh^{-1}\log(1/h))}$ calls, $2^{O(s^2d\log s)}$ if binary
-- statement:
--   There is a universal constant $a \in (0, 1]$ such that for every $0 < h < 1$ there is a deterministic algorithm $A_h$ with the following property. On every finite game $H$ (payoffs in $[0,1] \cap \mathbb Q$) accessed with $ah$-BR oracles, $A_h$ outputs a strategy pair with gap at most $h$ within
--   $$
--   2^{O(s^2 d\, h^{-1} \log(1/h))}
--   $$
--   oracle calls, where $s = s_H(ah)$ is a valid sparsification size and $d = d_H(ah)$ is the triangle dimension at margin $ah$. If $H$ is binary, the bound improves to
--   $$
--   2^{O(s^2 d \log s)} .
--   $$
--   This is the double-oracle analysis of Assos et al.; Theorem 2.1 runs $A_h$ with $h = 1/(4k)$ and bounds $s$ and $d$ by (22), (24) and the triangle-dimension bounds.
--
--   **Formalization Note** One program, reading $h$ from its input, serves every $h$; the bounds are $2^{C(1 + x)}$ with one universal $C$; they are required for every valid multiset size $s$ and every $d \ge d_H(ah)$.
--
--   Differences from the source:
--   - generalization: for every h a deterministic algorithm A_h → one program P with h in input cell 0 (inputH h); reason: fixing the input h gives an algorithm A_h for each h; Theorem 2.1 needs one algorithm for all k and runs A_{1/(4k)}
--   - reading: 2^{O(x)} calls → 2^{C(1 + x)} calls with one universal C; reason: the literal 2^{Cx} is false at s = 1 in the binary bound (x = 0 allows 1 call, but a pair needs a known row and a known column, hence two BR calls)
--   - encoding: s = s_H(ah), d = d_H(ah) → for every s with IsMultisetSize M (a*h) s and every d with TriangleDimLE M (a*h) d; reason: the bounds increase in s and d, so this is the bound at the least valid s and at d_H(ah); no junk-valued minimum or maximum
--   - encoding: a deterministic algorithm in the oracle model accessed with δ-BR oracles, against an adaptive adversary → one LiteralProgram of the real pointer machine (SmaleNinth core, rational literals) with utility, BR and halt instructions, run with every BRAdversary (answers indexed by the BR-call count, valid on every finite rational mixture); reason: the paper's model: steps are operations on rationals, strategies are known only through labels; for a fixed deterministic program a call-indexed adversary is as general as a history-dependent one
--   - encoding: oracle calls → utilCalls + brCalls of the halted state; reason: both oracles are counted, as in the paper
--   - encoding: maximizing or minimizing BR queries on ⊥ allowed initially → allowed at any time (a query with count 0); reason: an arbitrary answer to ⊥ is also a valid answer to a query on a point mass of a known strategy, so ⊥ queries give a program no extra power; no instance changes
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, Lemma C.1, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine
import Definitions.Def_NashOrTriangle_HaltsWith
import Definitions.Def_NashOrTriangle_IsPairAnswer
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_IsMultisetSize
import Definitions.Def_NashOrTriangle_TriangleDimLE
import Definitions.Def_NashOrTriangle_inputH

namespace NashOrTriangle

/-- **Lemma C.1** (Assos et al.). There is a universal `a ∈ (0, 1]` such that for every
`0 < h < 1` there is a deterministic algorithm `A_h` with the following property: on every
finite game `H` with `ah`-BR oracles, `A_h` outputs a strategy pair with gap at most `h` within
`2^{O(s² d h⁻¹ log(1/h))}` calls, where `s = s_H(ah)` and `d = d_H(ah)`; if `H` is binary, within
`2^{O(s² d log s)}` calls.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, Lemma C.1, printed p. 24 (PDF p. 25).

**Formalization Note** One program serves every `h` (given in input cell `0`); each printed
`A_h` is obtained by storing the literal `h` first. `2^{O(x)}` is `2^{C(1 + x)}` with one universal
`C`. `s` and `d` enter through the predicates: the bounds hold for every valid multiset size `s`
and every `d ≥ d_H(ah)`. "Calls" counts utility and BR calls. -/
theorem lemma_C1 :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ C : ℝ, ∃ P : Program, LiteralProgram P ∧
      ∀ h : ℝ, 0 < h → h < 1 →
      ∀ {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
        IsPayoff M → ∀ adv : BRAdversary M (a * h), ∀ s d : ℕ,
        IsMultisetSize M (a * h) s → TriangleDimLE M (a * h) d →
        HaltsWith P M adv (inputH h) (fun st => IsPairAnswer M h st ∧
            ((st.utilCalls + st.brCalls : ℕ) : ℝ) ≤
              (2 : ℝ) ^ (C * (1 + (s : ℝ) ^ 2 * (d : ℝ) * h⁻¹ * Real.log (1 / h)))) ∧
        (IsBinary M → HaltsWith P M adv (inputH h) (fun st => IsPairAnswer M h st ∧
            ((st.utilCalls + st.brCalls : ℕ) : ℝ) ≤
              (2 : ℝ) ^ (C * (1 + (s : ℝ) ^ 2 * (d : ℝ) * Real.log (s : ℝ))))) := by sorry

end NashOrTriangle
