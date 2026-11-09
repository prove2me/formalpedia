-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_proposition_4_10
-- name    : IntervalMaxCutEPTAS.Scheme.proposition_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:51.892028+00:00
-- url     : https://prove2.me/theorems/8a7b8a1b-5b37-409c-9259-8fcfd1dded26
-- title:
--   Proposition 4.10 — the structure in O(n²) time
-- statement:
--   There are a deterministic program and absolute constants such that, given an interval representation of an $n$-vertex graph $G$ with $m$ edges and an integer $b\ge4$, the program computes in time $O(n^2)$:
--
--   1. a set $Z$ of vertices and a spanning subgraph $H$ of $G$ with $|E(G)\setminus E(H)|\le 28\cdot2^{-b}m$ in which the vertices of $Z$ are isolated;
--   2. the hierarchy, and the partition of $V(G)\setminus Z$ into groups with their anchors and rounded intervals;
--   3. for every cell $C$ the sets $A(C)$, $R(C)$, the number $W(C)$, and for every child $C'$ of $C$ the set $O(C')\setminus O(C)$.
--
--   These are the objects of §4 for a ranking of the input (§4.1) and a shift satisfying Lemma 4.2, so they satisfy Lemmas 4.5 to 4.9.
--
--   Differences from the source:
--   - generalization: interval endpoints are real numbers → endpoints in an arbitrary linearly ordered type R; reason: the statement only uses comparisons of endpoints; taking R = ℝ gives the source statement
--   - encoding: time in the word-RAM model with constant-time endpoint comparisons → step count of a program of the published Light language (each primitive operation costs one step, including loads, arithmetic, tests and control flow); reason: explicit charged program syntax with constants quantified before all data; comparing two raw endpoints costs a constant number of steps
--   - encoding: O(n²) → C·(n + 1)²; reason: for n ≥ 1, (n+1)² ≤ 4n²; the +1 only keeps n = 0 meaningful
--   - encoding: no explicit space bound → space limit S bounded by the same expression; depth limit T; reason: Light runs need finite limits; the source's proof gives this space (PDF p. 19, 21), and a run of T steps cannot nest more than T calls
--   - reading: words of Θ(log n) bits → word limit (n + b + 2)^c; reason: read Θ(log n) with the numerical parameter fixed; the uniform bound also holds b as an input word, without changing the absolute O(n²) time bound
--   - encoding: “compute … these objects” → the memory holds exactly structList for some ranking ρ of the input and some shift θ < 2M with Lemma 4.2's bound; reason: a fixed output layout defined from the paper's objects; H is given by the rejected flags and rounded intervals, the hierarchy by M
--   - encoding: “These objects satisfy Lemmas 4.5 to 4.9” → not restated; the written objects are the defined ones; reason: Lemmas 4.5–4.9 are separate items about exactly these definitions
--   - encoding: the input interval representation, with constant-time endpoint comparisons → an integer representation J with SameComparisons I J, with correctness judged on I; reason: every finite endpoint order, including equalities, has an integer presentation; the universal quantifier over J permits no advice in its magnitudes, and sorting and relabelling cost O(n log n) comparisons within the stated bound
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Proposition 4.10, PDF p. 18 (printed p. 17); proof PDF p. 19

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Proposition 4.10, as a costed `Light` program: one program, with absolute constants, that for
every `n`, every integer `b ≥ 4` and every interval representation computes in `O(n²)` steps (and
space) the set `Z`, the edited graph (rounded intervals and rejected flags), the hierarchy (`M`),
the groups with their anchors and rounded intervals, and for every cell `C` the sets `A(C)`,
`R(C)`, the number `W(C)` and, for each child `C'`, the set `O(C') \ O(C)`, written in the layout
`structList`, for a rank representation of the input and a shift satisfying Lemma 4.2's bound,
so that `|E(G) \ E(H)| ≤ 28 · 2^{-b} m`. -/
theorem proposition_4_10 :
    ∃ (Prog : Light.Program) (C c : ℕ), ∀ (n b : ℕ), 4 ≤ b →
      ∀ {R : Type} [LinearOrder R] (I : Rep R n) (J : Rep ℤ n), SameComparisons I J →
        ∃ T S : ℕ, T ≤ C * (n + 1) ^ 2 ∧ S ≤ C * (n + 1) ^ 2 ∧
          Light.Ends ⟨(((n + b + 2) ^ c : ℕ) : ℤ), S, T⟩ Prog 0 entry
            (start (encodeStruct J b)) T (ReportsStructure I b S) := by sorry

end IntervalMaxCutEPTAS.Scheme
