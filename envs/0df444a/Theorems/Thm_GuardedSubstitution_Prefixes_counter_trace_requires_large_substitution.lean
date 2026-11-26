-- Prove2me | Theorems.Thm_GuardedSubstitution_Prefixes_counter_trace_requires_large_substitution
-- name    : GuardedSubstitution.Prefixes.counter_trace_requires_large_substitution
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T19:40:31.189906+00:00
-- url     : https://prove2.me/theorems/aafbdfed-1a95-439d-8988-840349d998bc
-- title:
--   Counter traces require many entries in explicit substitution levels
-- statement:
--   Fix integers $2 \le m \le B$. Form a binary trace by listing the $B$ low bits of every counter value from zero through $2^m-1$, least significant bit first. A finite table replaces each symbol by a word, and one starting symbol is expanded for $d$ simultaneous rounds. Take any prefix of this unprojected expansion and decode each symbol as either a single bit or the empty word. Suppose the resulting binary word starts with the entire counter trace. If $S$ is the sum of the lengths of all replacement words, then $2^m \le d S (m-1)$.
-- source:
--   Applies the factor-counting method of Charikar et al., The Smallest Grammar Problem, IEEE Transactions on Information Theory 51(7), 2005, Section IV, Lemma 3, https://web.cs.ucla.edu/~sahai/work/web/2005%20Publications/TransOnInfoTheory2005.pdf. This adaptation counts the explicit repeated levels of one substitution, allows erasing the terminal labels, and uses a counter trace as the witness.

import Definitions.Def_GuardedSubstitutionReadout

theorem GuardedSubstitution.Prefixes.counter_trace_requires_large_substitution {k : ℕ}
    (m block : ℕ) (wide : 2 ≤ m) (fits : m ≤ block)
    (rule : Fin k → List (Fin k)) (decode : Fin k → List Bool)
    (short : ∀ a, (decode a).length ≤ 1)
    (depth : ℕ) (a : Fin k) (T : ℕ) (tail : List Bool) :
    let trace : List Bool :=
      List.ofFn (fun t : Fin (block * 2 ^ m) => (t.val / block).testBit (t.val % block))
    trace ++ tail = ((GuardedSubstitution.Prefixes.expansion rule depth a).take T).flatMap decode →
      2 ^ m ≤ depth * (∑ b, (rule b).length) * (m - 1) := by sorry
