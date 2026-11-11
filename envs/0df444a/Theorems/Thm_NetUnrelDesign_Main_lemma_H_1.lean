-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_H_1
-- name    : NetUnrelDesign.Main.lemma_H_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:43.52842+00:00
-- url     : https://prove2.me/theorems/1ad2e74d-6771-4458-a921-896c1baafc49
-- title:
--   Lemma H.1 — candidate selection: Pr{u(x) ≤ U ≤ (1+16a)u*} ≥ 1 − δ in expected work O(B log(2/δ))
-- statement:
--   There are a constant $C>0$ and one program with a routine-oracle instruction such that the following holds. Fix $m$, a value function $u$ on $\mathbb R^m$, a candidate domain $D$, and $u^*>0$ with $u^*\le u(x)$ for all $x\in D$. Fix $0<a\le1/32$, $0<\delta\le1/2$, a supplied fallback point and $B\ge1$. The routines are run with fresh randomness at every call and satisfy:
--   1. a candidate call returns a point of $D$ or FAIL, with $\Pr\{x\ne{\rm FAIL},\ u(x)\le(1+a)u^*\}\ge3/4$;
--   2. at every $x\in D$, a value call returns $W$ with $\Pr\{|W-u(x)|\le a\,u(x)\}\ge63/64$;
--   3. every such call has expected cost at most $B$, including the work needed to return its output.
--
--   Given $m$, $a$, $\delta$ and the fallback, but not $u^*$, the program has the following properties.
--   - On every halting run it returns either a point of $D$ with a finite upper estimate $U$, or the fallback with $U=+\infty$.
--   - It calls the value routine only at points returned by earlier candidate calls, so never at the fallback.
--   - With probability at least $1-\delta$ it halts with $u(x)\le U\le(1+16a)u^*$ (H.1).
--   - Its expected work is at most $C\,B\log(2/\delta)$.
--   - The expected numbers of candidate calls and of value calls are each at most $C\log(2/\delta)$.
--
--   Differences from the source:
--
--   - generalization: u the unreliability of the paper's designs and a candidate domain of feasible designs → any real function u on ℝ^m and any set D ⊆ ℝ^m; the returned point is in D or is the fallback; reason: the selection uses only the values u(x); the source's case is a special case
--   - reading: 'an independent candidate call', 'a fresh base estimate W satisfies Pr{… | history, x} ≥ 63/64', 'conditional expected cost' → each routine is a fixed randomized procedure (a measurable oracle of the query and its own fresh tape); the per-call guarantees are stated for that procedure; reason: for a procedure run on fresh randomness the conditional guarantee given the history is exactly the per-call guarantee
--   - reading: 'On selection failure, it returns a supplied feasible fallback and U = +∞, without a value query at that point' → on the fallback outcome the output is the fallback with U = +∞; every value query of every run is at a point returned by an earlier candidate call; reason: a value query is never issued for the fallback
--   - encoding: "an algorithm … in expected work" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - encoding: U ∈ ℝ ∪ {+∞} → EReal: ⊤ when integer output cell 1 is nonzero, else real output cell 0; reason: the extended value
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma H.1, p. 55 (PDF 56)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators ENNReal Classical

namespace NetUnrelDesign.Main

/-- **Lemma H.1 (Candidate selection).** There are a constant `C > 0` and one program with a
routine-oracle instruction such that, for every `m`, every value function `u` on `ℝ^m`, every
candidate domain `D ⊆ ℝ^m`, every `u* > 0` that is a lower bound on `u` over `D`, every
`0 < a ≤ 1/32`, `0 < δ ≤ 1/2`, every supplied fallback point, every `B ≥ 1`, and every
(measurable, fresh-randomness) routine oracle such that (1) a candidate call returns a point of
`D` or FAIL, and returns a point `x` with `u(x) ≤ (1 + a)u*` with probability at least `3/4`;
(2) a value call at any `x ∈ D` returns `W` with `|W − u(x)| ≤ a u(x)` with probability at least
`63/64`; and every such call has expected cost at most `B`: the program, given `m`, `a`, `δ` and the
fallback (not `u*`), on every halting run returns either a point of `D` with a finite upper estimate
`U` or the fallback with `U = +∞`; it makes value calls only at points returned by earlier candidate
calls (in particular none at the fallback); with probability at least `1 − δ` it halts with
`u(x) ≤ U ≤ (1 + 16a)u*` (H.1); its expected work is at most `C B log(2/δ)`; and the expected
numbers of candidate calls and of value calls are each at most `C log(2/δ)`.
Sun 2026, p. 55 (PDF 56). -/
theorem lemma_H_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (m : ℕ) (u : (Fin m → ℝ) → ℝ) (D : Set (Fin m → ℝ)) (uStar : ℝ), 0 < uStar →
        (∀ x ∈ D, uStar ≤ u x) →
        ∀ a δ : ℝ, 0 < a → a ≤ 1 / 32 → 0 < δ → δ ≤ 1 / 2 →
          ∀ (xfb : Fin m → ℝ) (B : ℝ), 1 ≤ B →
            ∀ O : Oracle (routineSpec m), OracleMeasurable (routineSpec m) O →
              (∀ ω', (O (candQuery m) ω').1.1 = true → (O (candQuery m) ω').1.2.1 ∈ D) →
              uniformTape {ω' | ¬ ((O (candQuery m) ω').1.1 = true ∧
                  u (O (candQuery m) ω').1.2.1 ≤ (1 + a) * uStar)} ≤ ENNReal.ofReal (1 / 4) →
              (∀ x ∈ D, uniformTape {ω' | ¬ |(O (true, x) ω').1.2.2 - u x| ≤ a * u x} ≤
                  ENNReal.ofReal (1 / 64)) →
              ∫⁻ ω', ((O (candQuery m) ω').2 : ℝ≥0∞) ∂uniformTape ≤ ENNReal.ofReal B →
              (∀ x ∈ D, ∫⁻ ω', ((O (true, x) ω').2 : ℝ≥0∞) ∂uniformTape ≤ ENNReal.ofReal B) →
                OnEveryHalt P O (initState (routineSpec m) [(m : ℤ)] ([a, δ] ++ vecList xfb))
                    (fun s => (outInt s 1 = 0 → selectedPoint s ∈ D) ∧
                      (outInt s 1 ≠ 0 → selectedPoint s = xfb)) ∧
                OnEveryState P O (initState (routineSpec m) [(m : ℤ)] ([a, δ] ++ vecList xfb))
                    (fun s => ∀ (pre post : List ((Bool × (Fin m → ℝ)) × (Bool × (Fin m → ℝ) × ℝ)))
                      (c : (Bool × (Fin m → ℝ)) × (Bool × (Fin m → ℝ) × ℝ)),
                      s.transcript = pre ++ c :: post → c.1.1 = true →
                      ∃ c' ∈ pre, c'.1.1 = false ∧ c'.2.1 = true ∧ c'.2.2.1 = c.1.2) ∧
                failureProb P O (initState (routineSpec m) [(m : ℤ)] ([a, δ] ++ vecList xfb))
                    (fun s => ((u (selectedPoint s) : ℝ) : EReal) ≤ selectedU s ∧
                      selectedU s ≤ (((1 + 16 * a) * uStar : ℝ) : EReal)) ≤ ENNReal.ofReal δ ∧
                expectedWork P O (initState (routineSpec m) [(m : ℤ)] ([a, δ] ++ vecList xfb)) ≤
                  ENNReal.ofReal (C * B * Real.log (2 / δ)) ∧
                ∫⁻ ω, totalCallsWhere P O
                    (initState (routineSpec m) [(m : ℤ)] ([a, δ] ++ vecList xfb))
                    (fun q => q.1 = false) ω ∂jointLaw ≤ ENNReal.ofReal (C * Real.log (2 / δ)) ∧
                ∫⁻ ω, totalCallsWhere P O
                    (initState (routineSpec m) [(m : ℤ)] ([a, δ] ++ vecList xfb))
                    (fun q => q.1 = true) ω ∂jointLaw ≤ ENNReal.ofReal (C * Real.log (2 / δ)) := by sorry

end NetUnrelDesign.Main
