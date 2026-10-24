-- Prove2me | Theorems.Thm_OAI_WLTime_OneTape_Symbolic_RAMWriter_correct
-- name    : OAI.WLTime.OneTape.Symbolic.RAMWriter.correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:51:33.993465+00:00
-- url     : https://prove2.me/theorems/55dccdb0-03cd-46aa-a954-4c8ac8d2d757
-- title:
--   The diagonal consumer of a word RAM halts in quadratic time and accepts exactly when the RAM rejects the reduction's graph pair (OpenAI WL time lower bound)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of the unconditional time lower bound for Weisfeiler–Leman equivalence (`OAI.WLTime.unconditional_time_lower_bound`, the paper's Theorem 1.1): the correctness and running time of the diagonal consumer built from a sequential word RAM $A$ (`RAM`).
--
--   **Notation** (published bundle `Def_WeisfeilerLeman` and definitions bundle `OAIQWWLT000` of this split). Fix a one-tape machine $U$ (`OneTape`) and parameters $d, q$ with $d + q \ge 2$. For an input word $w$ with $|w| \ge 1$ and a padding $p$, `pairGraph U d q hr w p ε` ($\varepsilon \in \{0,1\}$) are the two graphs of OpenAI's computation reduction: the rectangular consistency graphs of the instance built from $U$ and $w$, with untwisted ($\varepsilon = 0$) or twisted ($\varepsilon = 1$) parity, listed as adjacency matrices on $\text{baseOrder}(U,d,q,|w|) + p$ vertices, where `baseOrder U d q m` $= 1 + Cm^2((Cm^2+1)^2+1)$ for the construction's coefficient $C$. `encodePair G H` is the bit string of the two adjacency matrices. For a machine $A$ and an order $n \ge \text{baseOrder}(U,d,q,|w|)$, put $y_s = $ `encodePair` of the two graphs with padding $p = n - \text{baseOrder}(U,d,q,|w|)$.
--
--   The consumer `consumer U d q A n` is a one-tape machine that, on input $w$, runs OpenAI's writer program (which computes $y_s$ from $w$ within the step budget `FullWriter.budget U d q n |w|`) and then simulates $A$ on $y_s$, accepting exactly when $A$ rejects. `consumerFactor U d q A` is an explicit constant depending on $U, d, q, A$ only.
--
--   **The statement.** Let $A$ be a word RAM (logarithmic word width), $w$ a word with $|w| \ge 1$, $n \ge \text{baseOrder}(U,d,q,|w|)$, $y_s$ as above, and suppose $A$ halts on $y_s$ at order $n$. Then the consumer for $A$ (the RAM version, `RAMWriter.consumer`, which simulates $A$ on a one-tape machine) halts on $w$, its running time on $w$ is at most
--   $$\text{consumerFactor}\cdot\bigl(|w| + \text{budget}(n, |w|) + 5|y_s| + \text{RAMAlphabet.budget}(A, \text{width}, |y_s|, T_A(n, y_s)) + 3\bigr)^2,$$
--   where $T_A(n, y_s)$ is the running time of $A$ and the width is $A$'s word width at order $n$, and it accepts $w$ if and only if $A$ does not accept $y_s$ at order $n$.
-- source:
--   OpenAI, Unconditional time lower bounds for Weisfeiler–Leman equivalence, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WeisfeilerLeman/RAMBounds.lean (declaration OAI.WLTime.OneTape.Symbolic.RAMWriter.correct)

import Mathlib
import Definitions.Def_WeisfeilerLeman
import Definitions.Def_OAIQWWLT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uX

namespace WLTime.OneTape.Symbolic.RAMWriter
open TypedStack
open scoped Classical
noncomputable section
variable (U : OneTape) (d q : ℕ) (A : RAM)
 theorem correct (n : ℕ) (w : List Bool) (hm : 1 ≤ w.length) (hr : 2 ≤ d+q)
    (hn : baseOrder U d q w.length ≤ n)
    (ys : List Bool) (hys : ys=encodePair (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
      (pairGraph U d q hr w (n-baseOrder U d q w.length) 1))
    (hh : A.halts n ys) :
    (consumer U d q A n).toTM.halts w ∧
    (consumer U d q A n).toTM.time w ≤ consumerFactor U d q A*
      (w.length+FullWriter.budget U d q n w.length+5*ys.length+
        RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)+3)^2 ∧
    ((consumer U d q A n).toTM.accepts w ↔ ¬A.accepts n ys) := by
  sorry
end
end WLTime.OneTape.Symbolic.RAMWriter

end OAI
end
