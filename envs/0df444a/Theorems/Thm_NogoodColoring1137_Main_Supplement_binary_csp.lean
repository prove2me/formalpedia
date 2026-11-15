-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_Supplement_binary_csp
-- name    : NogoodColoring1137.Main.Supplement.binary_csp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:57:57.883374+00:00
-- url     : https://prove2.me/theorems/7b34b429-dc3b-4b33-9df6-0dead798eb2a
-- title:
--   Theorem 5 — Binary CSPs with small independent sets
-- statement:
--   Let $I$ be an arbitrary binary CSP on $n$ ordered variables, each with ambient domain $\Sigma=\{0,1,2\}$, unary lists $L(v)\subseteq\Sigma$, and allowed relations $R_{vw}\subseteq\Sigma\times\Sigma$ for $v<w$. Let $Q_I$ be its satisfying assignments. Its constraint graph $H_I$ has an edge at a pair exactly when its full ambient relation is not $\Sigma\times\Sigma$. Let $\ell$ be any natural number satisfying $\alpha(H_I)<\ell$.
--
--   There exist two fixed deterministic programs, one for decision and one for search, and positive global constants $A,C$, independent of $\ell,n,I$, such that both tasks finish within
--
--   $$
--   A\exp\bigl(C\ell[\ln(n+1)]^2\bigr)
--   $$
--
--   bit steps. Decision returns one bit $b$, with $b=1$ if and only if $Q_I\ne\varnothing$. Search returns failure exactly when $Q_I=\varnothing$, and otherwise returns an actual assignment respecting every original unary and binary constraint.
--
--   The result is a companion application of domain reduction, beyond graph coloring. It asserts both decision and witness construction for every threshold; it does not assert exact counting. There is no diameter, complete constraint graph, relation-closure, nonempty-list, or colorability assumption.
--
--   **Formalization Note** Variables and colors use `Fin n` and the published `Color = Fin 3`. The solution family uses the published dependent `Code` with constant domain size three, retaining arbitrary unary lists as constraints. The graph uses the full relation before list filtering. Its independence number is Mathlib's finite-graph maximum. The canonical merged table encoding puts binary $n$ first and binary $\ell$ last. `Runs` measures actual executions on the published finite multitape model. All programs and positive constants precede every input. Natural logarithms change only the globally quantified constant $C$. No numerical leading or exponent implementation constant is specified by the paper. For $1\le\ell\le n$, §4.3 p.13 at $\sigma=3$ gives $K\le3\ell\ln(n+1)$ and at most $(n+1)^K$ boxes; construction and polynomial per-box work fit the stated exponent. The $\ell>n$ exhaustive branch and the $n=0$ empty-assignment branch remain included; the latter can ignore the trailing threshold. The promise already makes $\ell=0$ impossible. No nogood, independent-set, or 2-SAT oracle is assumed as an input.
--
--   Differences from the source:
--   - encoding: ordered finite variables with alphabet {0,1,2} and arbitrary merged unary and binary constraints → Fin n variables, the published Fin 3 palette, finite unary tables, one allowed relation per increasing pair, and the dependent solution code on full ambient domains; reason: bijective relabeling and merging preserve every source instance, including empty lists and nonsymmetric value relations
--   - encoding: deterministic decision and finding a solution in exp(O(ell log²(n+1))) time → two fixed finite multitape bit programs and positive global A,C before all thresholds and instances, each with actual execution bound A exp(C ell [ln(n+1)]²); reason: fixes the unspecified explicit table encoding and machine convention without changing the first power of ell or the squared logarithm; the proof has polynomial bit overhead absorbed in the same exponent
--   - encoding: a solution, if one exists, can be found within the same bound → a tagged satisfying assignment when one exists and a failure tag otherwise, also for n=0 and ell>n; reason: makes search output explicit; unsatisfiability is decided in the same bound and the empty assignment needs no scan of the trailing threshold
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Theorem 5, Section 8.1, pp. 23–24 (printed = PDF); construction bound Section 4.3, p. 13

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Supplement_CSPComputation

namespace NogoodColoring1137.Main.Supplement

/-- Theorem 5, pp.23–24: uniform deterministic decision and search, for all
thresholds and arbitrary unary and binary relations. The independence number
is only a promise, not an extra input or an algorithmic oracle. -/
theorem binary_csp :
    ∃ (decision search : IntMul.MultitapeTM) (A C : ℝ),
      0 < A ∧ 0 < C ∧
      ∀ (ell n : ℕ) (I : CSP n), (ConstraintGraph I).indepNum < ell →
        (∃ b : Bool,
          Runs decision (EncodeCSP I ell) [b] (CSPTime A C ell n) ∧
          (b = true ↔ (SolutionCode I).Nonempty)) ∧
        (∃ out : List Bool,
          Runs search (EncodeCSP I ell) out (CSPTime A C ell n) ∧
          CSPSearchAnswer I out) := by sorry

end NogoodColoring1137.Main.Supplement
