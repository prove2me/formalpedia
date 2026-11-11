-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_5_3
-- name    : NetUnrelDesign.Main.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:10:39.993402+00:00
-- url     : https://prove2.me/theorems/e5780ce2-3d3f-4176-bcd6-5ef58afd04c2
-- title:
--   Lemma 5.3 — additive-one maximization of a concave ψ by cutting planes in expected work O(d(S + d²) log(2 + dR/r))
-- statement:
--   There are an absolute constant $C>0$ and one program with a value/supergradient-oracle instruction such that the following holds. Let $d\ge1$ and let $P_0\subseteq\mathbb R^d$ be compact and convex, inside a known outer Euclidean ball of center $c_0$ and radius $R>0$. Let $\psi$ be concave on $P_0$ and $\psi^*=\max_{P_0}\psi$. Let $r>0$ be such that $K_{1/2}=\{y\in P_0:\psi(y)\ge\psi^*-1/2\}$ contains a Euclidean ball of radius $r$. Let $h_0\in P_0$ be a supplied feasible point. Let the oracle at $h\notin P_0$ return a feasibility separator, and at $h\in P_0$ return the exact value $\psi(h)$ and a supergradient, each query costing at most $S$. Given $d$, $c_0$, $R$, $r$ and $h_0$, but neither $\psi^*$ nor the center of the ball in $K_{1/2}$, the program returns, on every halting run, a point $h_{\rm best}\in P_0$ with $\psi(h_{\rm best})\ge\psi^*-1$. Its expected work is at most $Cd(S+d^2)\log(2+dR/r)$.
--
--   Differences from the source:
--
--   - encoding: "the algorithm" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - encoding: ψ* = max_{P₀} ψ → sSup (ψ '' P₀); reason: P₀ is nonempty and a concave function on a bounded convex set is bounded above; the supremum is the maximum when attained
--   - encoding: a query returns a feasibility separator or the exact value and a supergradient → a deterministic oracle: off P₀ a vector g ≠ 0 with ⟨g, z⟩ ≤ ⟨g, h⟩ on P₀; on P₀ the value ψ(h) and g with ψ(z) ≤ ψ(h) + ⟨g, z − h⟩ on P₀; cost ≤ S; reason: the oracle of the statement
--   - reading: 'returns a feasible point h_best with ψ(h_best) ≥ ψ* − 1, in expected work …' → the guarantee holds on every halting run; reason: §5.4: both cutting-plane computations check containment and restart failed trials, 'so their outputs are always correct'
--   - encoding: 'in a known outer ball of radius R' → a closed Euclidean ball {‖y − c₀‖₂ ≤ R} with R > 0, center c₀ and R given as inputs; reason: a known ball is given by its center and its (positive) radius
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 5.3, p. 17 (PDF 18)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces

open scoped BigOperators ENNReal

namespace NetUnrelDesign.Main

/-- **Lemma 5.3 (Additive-one optimization).** There are an absolute constant `C > 0` and one
program with a value/supergradient-oracle instruction such that, for every `d ≥ 1`, every compact
convex `P₀ ⊆ ℝ^d` in a known outer Euclidean ball `B(c₀, R)` (`R > 0`), every `ψ` concave on `P₀` with
`ψ* = max_{P₀} ψ` (written `sSup`), every `r > 0` such that
`K_{1/2} = {y ∈ P₀ : ψ(y) ≥ ψ* − 1/2}` contains some Euclidean ball of radius `r`, every supplied
feasible point `h₀ ∈ P₀`, and every deterministic oracle that at `h ∉ P₀` returns a feasibility
separator and at `h ∈ P₀` returns the exact value `ψ(h)` and a supergradient, each query costing at
most `S`: the program, given `d`, `c₀`, `R`, `r` and `h₀` (not `ψ*`, not the ball's center), on
every halting run returns `h_best ∈ P₀` with `ψ(h_best) ≥ ψ* − 1`, in expected work at most
`C d(S + d²) log(2 + dR/r)`. Sun 2026, p. 17 (PDF 18). -/
theorem lemma_5_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (P0 : Set (Fin d → ℝ)), IsCompact P0 → Convex ℝ P0 →
        ∀ (c0 : Fin d → ℝ) (R : ℝ), 0 < R → P0 ⊆ eBall c0 R →
          ∀ ψ : (Fin d → ℝ) → ℝ, ConcaveOn ℝ P0 ψ →
            ∀ r : ℝ, 0 < r →
              (∃ c1 : Fin d → ℝ, eBall c1 r ⊆ {y | y ∈ P0 ∧ sSup (ψ '' P0) - 1 / 2 ≤ ψ y}) →
              ∀ h0 ∈ P0, ∀ O : Oracle (valSpec d), OracleDeterministic (valSpec d) O →
                ValueOracleValid P0 ψ O → ∀ S : ℝ, CostAtMost S O →
                  OnEveryHalt P O
                      (initState (valSpec d) [(d : ℤ)] (vecList c0 ++ [R, r] ++ vecList h0))
                      (fun s => outVec s 0 d ∈ P0 ∧ sSup (ψ '' P0) - 1 ≤ ψ (outVec s 0 d)) ∧
                  expectedWork P O
                      (initState (valSpec d) [(d : ℤ)] (vecList c0 ++ [R, r] ++ vecList h0)) ≤
                    ENNReal.ofReal
                      (C * d * (S + (d : ℝ) ^ 2) * Real.log (2 + d * R / r)) := by sorry

end NetUnrelDesign.Main
