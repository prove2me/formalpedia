-- Prove2me | Theorems.Thm_LogStarBinPacking_lemma_3_2
-- name    : LogStarBinPacking.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:45.93047+00:00
-- url     : https://prove2.me/theorems/ab770b1b-36ef-417d-b608-928ad1ee9ee9
-- title:
--   Lemma 3.2 — a $d$-admissible tree in time $S_d^{O(1)}$ with $S_d\le T_{4d+2}$
-- statement:
--   Given an integer $d\ge1$, one can deterministically construct a $d$-admissible tree, its marked copies, and integers $p_1,\dots,p_L$, $D_*$, $S_d$ in time $S_d^{O(1)}$, where
--   $$
--   \max\{d,\,L,\,P,\,D_*,\,H\}\ \le\ S_d\ \le\ T_{4d+2}.
--   $$
--   Here $P=\sum_\ell p_\ell$, $H=|V(T^+)|+|V(T^-)|$ and $T_j$ is the tower sequence.
--
--   This bounds the competing trees of [OAI26] by a tower of height linear in $d$, which is what lets the gap grow like $\log^*n$.
--
--   **Formalization Note** The algorithm is one Turing machine reading $d$ in binary and writing the encoded record; its running time is at most $S_d^e$ steps for one exponent $e$ fixed before $d$.
--
--   Differences from the source:
--   - encoding: a finite rooted tree and its copies → the sets of leaf addresses (lists of naturals); copies labelled by original addresses; reason: every finite rooted tree with leaves at one depth has such a labelling
--   - reading: time S_d^{O(1)} → at most S_d^e steps, e fixed before d; reason: S_d ≥ H ≥ 4, so any bound C·S_d^k is at most S_d^e for a larger e
--   - encoding: "deterministically construct" → one FinTM2 with a finite alphabet mapping the binary encoding of d to the encoded record; reason: the standard Turing-machine model
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Lemma 3.2, p.13

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_tower
import Definitions.Def_LogStarBinPacking_AdmissibleTreeData

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Lemma 3.2 (tree size).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Lemma 3.2, p.13 (definition of `d`-admissible trees,
p.13; tower sequence (3.2), p.13). Given an integer `d ≥ 1`, one can deterministically
construct a `d`-admissible tree, its marked copies, and integers `p₁, …, p_L, D∗, S_d` in time
`S_d^{O(1)}`, where `max{d, L, P, D∗, H} ≤ S_d ≤ T_{4d+2}`.

**Formalization Note** One deterministic machine (a Mathlib `FinTM2` with Boolean input and output
alphabets and a finite alphabet) reads the binary encoding `natBits d` and writes the encoding of an
`AdmissibleTreeData` record (tree, markings, copies, their marks, `L`, `[p₁, …, p_L]`, `D∗`,
`S_d`) that `IsAdmissible d`. The time `S_d^{O(1)}` is `S_d^e` steps for one exponent `e`
fixed before `d` (`TM2OutputsInTime` is data, so its existence is `Nonempty`). `P = ∑ p_ℓ`, `H = |V(T⁺)| + |V(T⁻)|`, `T_j` is `tower j`. -/
theorem lemma_3_2 :
    ∃ e : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      MachineFiniteAlphabet.FiniteAlphabet M.tm ∧
      ∀ d : ℕ, 1 ≤ d → ∃ o : AdmissibleTreeData,
        o.IsAdmissible d ∧
        d ≤ o.sizeBound ∧ o.depth ≤ o.sizeBound ∧ o.P ≤ o.sizeBound ∧
        o.branchBound ≤ o.sizeBound ∧ o.H ≤ o.sizeBound ∧
        o.sizeBound ≤ tower (4 * d + 2) ∧
        Nonempty (Turing.TM2OutputsInTime M.tm
          (List.map M.inputAlphabet.invFun (BinaryEncoding.natBits d))
          (some (List.map M.outputAlphabet.invFun o.bits)) (o.sizeBound ^ e)) := by sorry

end LogStarBinPacking
