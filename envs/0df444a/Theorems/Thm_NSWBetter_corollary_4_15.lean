-- Prove2me | Theorems.Thm_NSWBetter_corollary_4_15
-- name    : NSWBetter.corollary_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:58:01.751901+00:00
-- url     : https://prove2.me/theorems/45f814e6-247a-4864-b093-c039829c26a6
-- title:
--   Corollary 4.15 — the well-behaved agents can be found in polynomial time
-- statement:
--   There is a polynomial-time algorithm which, given an instance $I$ with nonnegative rational values and a rational fractional allocation $x$ (row-major list), outputs for each agent $i$ whether $x$ is well-behaved for $i$ (Definition 4.14):
--   $$A(I,x)=\bigl(\mathbb 1\{x\text{ is well-behaved for }i\}\bigr)_{i\in N}.$$
--
--   It is used to decide which of the algorithms of Sections 4–6 applies (proof of Theorem 1.1, p.48).
--
--   Differences from the source:
--   - encoding: a fractional allocation $x$ given to an algorithm → a rational matrix given as a row-major list, the instance $I$ also part of the input; reason: an algorithm's input is finite; same inputs
--   - encoding: "polynomial time algorithm" → `Turing.TM2ComputableInPolyTime` over fixed binary encodings, output the indicator list; reason: Mathlib's Turing-machine model; binary numbers make the input length the bit size
--   - reading: "$I_{i,x}(\Delta)$ is well-behaved for all feasible $\Delta$" → for every $\Delta\ge1$ with all $\Delta x_{ig}$ integral; reason: by Lemma 4.12 well-behavedness is the same for every such $\Delta$ and feasible $\Delta$ exist for rational $x$
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Corollary 4.15, p.25

import Mathlib
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Inst_WellFormed
import Definitions.Def_NSWBetter_Inst_rv
import Definitions.Def_NSWBetter_IsFrac
import Definitions.Def_NSWBetter_WellBehavedAgent
import Definitions.Def_NSWBetter_encInstFrac
import Definitions.Def_NSWBetter_encBools
import Definitions.Def_NSWBetter_decodeFrac

namespace NSWBetter

open Classical in
/-- **Corollary 4.15.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Corollary 4.15, p.25: "Given a fractional allocation x, there is a polynomial time algorithm that can efficiently identify the set of well-behaved agents in x."

There is a Turing machine, polynomial time in the binary input `(I, x)`, that outputs the indicator list of the agents for which `x` is well-behaved (Definition 4.14), for every well-formed instance and every rational fractional allocation `x`.

**Formalization Note.** The fractional allocation is rational (an algorithm's input), given row-major. Footnote 6, p.23, explains the comparison with `1 − 1/e` in Property A. -/
theorem corollary_4_15 :
    ∃ A : Inst × List ℚ → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encInstFrac encBools A) ∧
      ∀ I : Inst, I.WellFormed → ∀ xs : List ℚ,
        IsFrac (fun i g => ((decodeFrac I xs i g : ℚ) : ℝ)) →
        A (I, xs) = List.ofFn fun i =>
          decide (WellBehavedAgent I.rv (fun i g => ((decodeFrac I xs i g : ℚ) : ℝ)) i) := by sorry

end NSWBetter
