-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_binary_greedy_lower_bound
-- name    : GreedySuperstring.LowerBound.binary_greedy_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:18.919309+00:00
-- url     : https://prove2.me/theorems/7fd0ad53-045c-4699-86f4-44db710a1b3b
-- title:
--   Theorem 4.1 — exact binary greedy lower-bound witnesses
-- statement:
--   For every pair of integers $r\ge1$ and $P\ge r-1$, there exist a finite substring-free set $\mathcal S$ of exactly $5r$ nonempty binary words and binary common superstrings $H$ and $g$ such that $g$ is the output of a complete legal maximum-overlap greedy execution on $\mathcal S$, and
--
--   $$|H|=5Pr+27r^2+4P+19r+1,\qquad |g|=12Pr+\frac{115r^2+7r}{2}.$$
--
--   Both lengths are exact. The tie-breaking execution is existential; no claim is made that all outputs on this same input have the displayed length. The shorter witness need not be optimal. In particular, the parameter pair $(r,P)=(1,0)$ is included and gives lengths $47$ and $61$.
--
--   The result supplies the paper's binary lower bound approaching twelve fifths of the optimum. The exact finite-instance assertion is retained as the goal rather than replaced by that asymptotic consequence. Coverage uses the published ordinary contiguous-substring predicate, with the finite input set enumerated as a list.
--
--   Differences from the source:
--   - encoding: integers r ≥ 1 and P ≥ r−1 → natural numbers r and P with 1 ≤ r and r ≤ P+1; reason: the source domain already forces both parameters nonnegative, including r=1 and P=0
--   - encoding: binary symbols 0 and 1 → the distinct symbol labels [false] and [true] in OAI.Superstring.Word; reason: this renaming preserves contiguous occurrences and counts one symbol per bit, without bit-encoding lengths
--   - encoding: a finite input set and an attainable complete greedy output → a Finset input enumerated by toList for published coverage and a singleton-ending run with concatenated histories; reason: list order does not affect universal coverage; histories only annotate the same maximum-overlap updates and existentially quantify all tie choices
--   - encoding: the integer-valued fraction (115r²+7r)/2 → natural division (115*r^2+7*r)/2; reason: r(115r+7) is even: r even supplies a factor two, and r odd makes 115r+7 even, so division is exact for every permitted r
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, Theorem 4.1, printed p.14 = PDF p.14; standing substring-free/nonempty convention p.5; construction and witnesses pp.16–21; informal Theorem 1.1 p.3

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Construction

namespace GreedySuperstring.LowerBound

/-- Theorem 4.1, printed/PDF p.14. Both witnesses have exact lengths.
The source's integer domain is exactly the natural domain below, including (1,0).
The numerator 115*r^2+7*r is even for every natural r. -/
theorem binary_greedy_lower_bound (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1) :
    ∃ (S : Finset OAI.Superstring.Word) (H g : OAI.Superstring.Word),
      S.card = 5 * r ∧
      (∀ s ∈ S, IsBinary s ∧ s ≠ []) ∧ SubstringFree S ∧
      IsBinary H ∧ IsBinary g ∧
      OAI.Superstring.IsCommonSuperstring S.toList H ∧
      OAI.Superstring.IsCommonSuperstring S.toList g ∧
      IsGreedyOutput S g ∧
      H.length = 5 * P * r + 27 * r ^ 2 + 4 * P + 19 * r + 1 ∧
      g.length = 12 * P * r + (115 * r ^ 2 + 7 * r) / 2 := by sorry

end GreedySuperstring.LowerBound
