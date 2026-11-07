-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_24
-- name    : MultiSelectPandora.lemma_3_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:07.932928+00:00
-- url     : https://prove2.me/theorems/73c10e5a-0775-4c83-b1a1-d41e6999268a
-- title:
--   Lemma 3.24 — $I^{SL}$ satisfies (C1)–(C4), and $\mathrm{MAX}^{SL}=\mathrm{OPT}^{SL}$
-- statement:
--   There is a function $C$ such that for all $k\ge1$ and every rational $\varepsilon\in(0,1)$ there is a bound $L_0$, depending on $k$ and $\varepsilon$ only, such that the following holds for every valid rational instance with $0<\mathrm{OPT}$. Every table $S$ of $I^{SL}$ is well formed, has $L\le L_0$ states, which is (C1), and, if $\varepsilon\le1/4$,
--   $$L\le C(k)\Big(\frac1\varepsilon\Big)^{2k}$$
--   states (the count $O(\varepsilon^{-2k})$); it satisfies (C2), (C3) and (C4) with constant $1$, has $\mathrm{MAX}=\mathrm{OPT}$, and its optimum is $\mathrm{OPT}_{I^{SL}}$.
--
--   So Fact 3.3 applies to $I^{SL}$.
--
--   Differences from the source:
--   - reading: (C1) "constant size", "O(1/ε²) levels", "O(ε^{−2k})" states → L ≤ L₀ with L₀ depending on k and ε only, and the bound C(k)(1/ε)^{2k} for ε ≤ 1/4, with C depending on k only; reason: (C1) is "constant for constant k and fixed ε" (p.32); O(ε^{−2k}) is read as ε → 0, and the proof gives at most 2/ε² levels on ε ≤ 1/4, so C(k) = (2k)^k works
--   - reading: a fixed ε > 0 → ε < 1; reason: p.14 defines b_i through "E[vi] ≤ OPT ≤ εθ < θ", which needs ε < 1; otherwise b_i need not be a small level and I^SL is not a table over its stated levels
--   - encoding: I^SL as an SSDP → any rational table of I^SL, with every numbering that extends the componentwise order; reason: p.8 allows "any total order"
--   - encoding: no hypothesis on OPT → 0 < OPT; reason: θ = OPT^/ε is 0 when OPT = 0 and p.14 divides by it, so this excludes only an undefined case
--   - reading: the grid of Definition 3.21 written with ε OPT → the grid with ε OPT^; reason: footnote 1: "the algorithm uses ε OPT^", as OPT is not known; Φ changes by at most 2ε OPT within a cell
--   - reading: ⊤ is "an arbitrary fixed number greater than MaxV" (footnote 2) → ⊤ is a number above MaxV and above every value of the instance; reason: Remark A.4 and Claim A.7 need D^L(v) ≥ v for every v; with ⊤ = MaxV + 1 Claim 3.30 fails (two boxes, value 1000 with probability 0.1, else 0, c = 90, k = 1, ε = 1/4; gap 5.23)
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.24, p.16 (PDF p.17); proof p.32 (PDF p.33)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_RawInst_Valid
import Definitions.Def_MultiSelectPandora_RawInst_toInst
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_ISL
import Definitions.Def_MultiSelectPandora_DPData_value
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_Valid
import Definitions.Def_MultiSelectPandora_RawSSDP_C2
import Definitions.Def_MultiSelectPandora_RawSSDP_C3
import Definitions.Def_MultiSelectPandora_RawSSDP_C4
import Definitions.Def_MultiSelectPandora_RawSSDP_OPT
import Definitions.Def_MultiSelectPandora_RawSSDP_MAX
import Definitions.Def_MultiSelectPandora_IsISLtable

namespace MultiSelectPandora

/-- **Lemma 3.24**, p.16 (PDF p.17); proof p.32 (PDF p.33). Beyhaghi–Han–Luqman manuscript.

`I^SL` satisfies (C1)–(C4), and `MAX^SL = OPT^SL`.

**Formalization Note.** Every clause is for every fixed `ε ∈ (0, 1)`; `ε < 1` is needed for `I^SL` to be a table (`b_i < θ`, p.14). (C1), "constant size for constant `k` and fixed `ε`", is the bound `L ≤ L₀` with `L₀` depending on `k` and `ε` only, fixed before the instance. The paper's count `O(ε^{−2k})` (p.16) is the further clause `L ≤ C(k) (1/ε)^{2k}` for small `ε`, with `C` depending on `k` only: the proof gives at most `2/ε²` levels for `ε ≤ 1/4`, so `C k = (2k)^k` works. (C4) holds with `D = 1`. Any numbering of the states is covered. -/
theorem lemma_3_24 :
    ∃ C : ℕ → ℝ, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℚ, 0 < ε → ε < 1 → ∃ L₀ : ℕ, ∀ I : RawInst, I.Valid →
      0 < OPT I.toInst k → ∀ S : RawSSDP, IsISLtable ε k I S →
        S.Valid ∧ S.L ≤ L₀ ∧ (ε ≤ 1 / 4 → (S.L : ℝ) ≤ C k * (1 / (ε : ℝ)) ^ (2 * k)) ∧
          S.C2 ∧ S.C3 ∧ S.C4 1 ∧ S.MAX = S.OPT ∧
          S.OPT = (ISL I.toInst k ε).value Finset.univ (0 : Fin k → ℝ) := by sorry

end MultiSelectPandora
