-- Prove2me | Theorems.Thm_OAI_WLTime_OneTape_Symbolic_FullWriter_consumer_correct
-- name    : OAI.WLTime.OneTape.Symbolic.FullWriter.consumer_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:51:36.911637+00:00
-- url     : https://prove2.me/theorems/dcf4496e-bdc1-4949-830c-4bbf06135e5e
-- title:
--   The diagonal consumer of a multitape Turing machine halts in quadratic time and accepts exactly when the machine rejects the reduction's graph pair (OpenAI WL time lower bound)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of the unconditional time lower bound for Weisfeiler–Leman equivalence (`OAI.WLTime.unconditional_time_lower_bound`, the paper's Theorem 1.1): the correctness and running time of the diagonal consumer built from a multitape Turing machine $A$ (`TM`).
--
--   **Notation** (published bundle `Def_WeisfeilerLeman` and definitions bundle `OAIQWWLT000` of this split). Fix a one-tape machine $U$ (`OneTape`) and parameters $d, q$ with $d + q \ge 2$. For an input word $w$ with $|w| \ge 1$ and a padding $p$, `pairGraph U d q hr w p ε` ($\varepsilon \in \{0,1\}$) are the two graphs of OpenAI's computation reduction: the rectangular consistency graphs of the instance built from $U$ and $w$, with untwisted ($\varepsilon = 0$) or twisted ($\varepsilon = 1$) parity, listed as adjacency matrices on $\text{baseOrder}(U,d,q,|w|) + p$ vertices, where `baseOrder U d q m` $= 1 + Cm^2((Cm^2+1)^2+1)$ for the construction's coefficient $C$. `encodePair G H` is the bit string of the two adjacency matrices. For a machine $A$ and an order $n \ge \text{baseOrder}(U,d,q,|w|)$, put $y_s = $ `encodePair` of the two graphs with padding $p = n - \text{baseOrder}(U,d,q,|w|)$.
--
--   The consumer `consumer U d q A n` is a one-tape machine that, on input $w$, runs OpenAI's writer program (which computes $y_s$ from $w$ within the step budget `FullWriter.budget U d q n |w|`) and then simulates $A$ on $y_s$, accepting exactly when $A$ rejects. `consumerFactor U d q A` is an explicit constant depending on $U, d, q, A$ only.
--
--   **The statement.** Let $A$ be a multitape Turing machine, $w$ a word with $|w| \ge 1$, $n \ge \text{baseOrder}(U,d,q,|w|)$, $y_s$ as above, and suppose $A$ has halted on $y_s$ after $v$ steps. Then the consumer for $A$ (the Turing-machine version, `FullWriter.consumer`) halts on $w$, its running time on $w$ is at most
--   $$\text{consumerFactor}\cdot\bigl(|w| + \text{budget}(n, |w|) + 5|y_s| + (8\,\text{tapes}(A) + 2)\,v + 3\bigr)^2,$$
--   and it accepts $w$ if and only if $A$ does not accept $y_s$.
-- source:
--   OpenAI, Unconditional time lower bounds for Weisfeiler–Leman equivalence, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WeisfeilerLeman/Consumer.lean (declaration OAI.WLTime.OneTape.Symbolic.FullWriter.consumer_correct)

import Mathlib
import Definitions.Def_WeisfeilerLeman
import Definitions.Def_OAIQWWLT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uB

namespace WLTime.OneTape.Symbolic.FullWriter
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (U : OneTape) (d q : ℕ)
 theorem consumer_correct (A : TM) (n : ℕ) (w : List Bool) (hm : 1 ≤ w.length) (hr : 2 ≤ d+q)
    (hn : baseOrder U d q w.length ≤ n)
    (ys : List Bool) (hys : ys = encodePair (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
      (pairGraph U d q hr w (n-baseOrder U d q w.length) 1))
    (v : ℕ) (hv : A.halted (A.run ys v)) :
    (consumer U d q A n).toTM.halts w ∧
    (consumer U d q A n).toTM.time w  ≤
      consumerFactor U d q A*(w.length+budget U d q n w.length+5*ys.length+(8*A.tapes+2)*v+3)^2 ∧
    ((consumer U d q A n).toTM.accepts w ↔ ¬A.accepts ys) := by
  sorry

end WLTime.OneTape.Symbolic.FullWriter

end OAI
end
