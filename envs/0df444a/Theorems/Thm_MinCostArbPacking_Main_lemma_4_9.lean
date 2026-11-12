-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_9
-- name    : MinCostArbPacking.Main.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:12.912197+00:00
-- url     : https://prove2.me/theorems/37989483-82a8-4800-9067-0fdc29ca3276
-- title:
--   Lemma 4.9 — parametrized running time of Algorithm 1
-- statement:
--   **Lemma 4.9 (Parametrized running time).** Suppose each phase finds all proposals in $O(S(N,M))$ time and a largest compatible set of terminals in time $\Sigma$, where $S(N,M)\ge N+M$. Then the entire algorithm runs in
--
--   $$O\Big(k\log(kn)\cdot\big(S(N,M)+\Sigma+k^3n\log(kn)\big)+km\log n\Big)\tag{4.2}$$
--
--   time. Formally: there is an absolute constant $C$ such that for every program computing the proposals of a phase (shortest augmenting paths from one deficient vertex per deficient block, or the report that one of them has none) within $S(n,m,k)\ge n+m$ steps, and every program computing Algorithm 2's output on contracted graphs with $t\le n$ vertices and at most $k(t-1)$ arcs within $\Sigma(n,m,k)$ steps, some program solves minimum-cost $k$-arborescence packing (output as in Theorem 1.1) within $C$ times (4.2).
--
--   Differences from the source:
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - reading: "each phase finds all proposals in $O(S(N,M))$ time and a largest compatible set in time $\Sigma$" → programs meeting the proposal specification within $S(n,m,k)$ steps and Algorithm 2's specification within $\Sigma(n,m,k)$ steps are given; the conclusion is the existence of a program built from them; reason: subroutine bounds as functions of the instance parameters; this is how the lemma is applied with $S=O(m+kn\log n\log(kn))$ and $\Sigma=O(k^3n\log(kn))$
--   - reading: $S(N,M)\ge N+M$ for the search graph size → $S(n,m,k)\ge n+m$; reason: the search graph has a vertex for every element and every head vertex
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.2.4, p.14, Lemma 4.9

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.9 (Parametrized running time), p.14: suppose a program finds all proposals of a phase
within `S` steps and a program finds a largest compatible set of terminals (Algorithm 2's output)
within `Σ` steps, where `S ≥ n + m`. Then there is a program for the whole algorithm (Algorithm 1)
running in `O(k log(kn)·(S + Σ + k³ n log(kn)) + km log n)` steps, with an absolute constant. -/
theorem lemma_4_9 : ∃ C : ℝ, ∀ (Pprop Pext : Machine.Program) (cp ce : ℕ)
    (S Sig : ℕ → ℕ → ℕ → ℝ),
    (∀ n m k : ℕ, ((n : ℝ) + m) ≤ S n m k) →
    (∀ Y : PhaseInput, 1 ≤ Y.X.k → Y.ProposalPre → ∀ W : ℤ, ((Y.X.size + 2 : ℕ) : ℤ) ^ cp ≤ W →
      Machine.HaltsWithin Pprop W Y.inI Y.inR (S Y.X.n Y.X.m Y.X.k)
        (fun o _ => Y.ProposalOutput o)) →
    (∀ n m : ℕ, ∀ Z : ExtendInput, 1 ≤ Z.k → 1 ≤ Z.t → Z.t ≤ n → Z.h ≤ Z.k * (Z.t - 1) → Z.Pre →
      ∀ W : ℤ, ((Z.size + 2 : ℕ) : ℤ) ^ ce ≤ W →
        Machine.HaltsWithin Pext W Z.inI [] (Sig n m Z.k) (fun o _ => ExtendOutput Z o)) →
    ∃ (P : Machine.Program) (cw : ℕ), ∀ X : Instance, 2 ≤ X.n → 1 ≤ X.k →
      ∀ W : ℤ, ((X.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
        Machine.HaltsWithin P W X.inI X.inR
          (C * ((X.k : ℝ) * logL ((X.k : ℝ) * X.n) *
              (S X.n X.m X.k + Sig X.n X.m X.k + (X.k : ℝ) ^ 3 * X.n * logL ((X.k : ℝ) * X.n)) +
            (X.k : ℝ) * X.m * logL X.n))
          (fun o _ => PackingOutput X o) := by sorry

end MinCostArbPacking.Main
