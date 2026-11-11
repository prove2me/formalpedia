-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_4_2
-- name    : NetUnrelDesign.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:50.897841+00:00
-- url     : https://prove2.me/theorems/94356e3a-13c7-46ec-9ff1-e5460650502a
-- title:
--   Lemma 4.2 — a near-cut list with log h_x(x) and ∇log h_x(x) in expected cost (4.5); coverage w.p. ≥ 1 − p gives (4.6)
-- statement:
--   Assume the standing data of §4: an instance satisfying (1.1), $0<\varepsilon\le1/2$, a value $\lambda_0$ passing the branch test (5.8), $Q_0=X\cap\{\lambda\ge\lambda_0-B\}$ with $B=1+\log M$, and $\alpha,\sigma,\tau$ as in (4.3) with $a=\varepsilon/16$. There are one program, which uses no oracle, and one constant $C$ with the following property. At every $x\in Q_0$ and for every $0<p\le1/2$, the program is given the graph, $q^0$, $x$, $\varepsilon$, $\lambda_0$ and $p$, and:
--   - on every halting run it returns a nonempty, duplicate-free list $H_x$ of cuts, the value $\log h_x(x)$ and all $m$ coordinates of $\nabla\log h_x(x)$, where $h_x(y)=\sum_{C\in H_x}e^{-w_y(C)}$; moreover $h_x(y)>0$ and $h_x(y)\le z(y)$ for all $y$;
--   - with probability at least $1-p$, it halts with a list containing every cut of weight at most $\alpha\lambda(x)$;
--   - on this event, $(1-\tau)u(x)\le h_x(x)\le(1+\tau)u(x)$ (4.6);
--   - its expected cost is at most $C\,m^2[\sigma^{-2}\log(2m)+\sigma^{-1}\log^2(2m/(p\sigma))]$ (4.5).
--
--   Differences from the source:
--
--   - generalization: §4 standing data: the prepared output of Lemma 5.1 ((5.2), (5.3), the rounding (5.6)) with λ₀ passing (5.8) → only λ₀ with (5.8), 0 < ε ≤ 1/2 and x ∈ Q₀; reason: the routine and (4.6) use only λ(x) ≥ λ₀ − B ≥ 6 log n + 2 log(256/a) (through (4.4) and 1 < α < 3/2); every prepared datum satisfies these hypotheses
--   - encoding: "a routine returns" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - encoding: with probability at least 1 − p the list contains every cut of weight at most αλ(x) → the set of runs that do not halt with such a list has measure at most p; reason: non-halting counts as failure
--   - encoding: the logarithmic value log h_x(x) and all m coordinates of ∇log h_x(x) → real output cell 0 equals log h_x(x) and real output cell 1+e equals the Fréchet derivative of log h_x at x applied to the e-th unit vector, exactly; reason: exact real arithmetic with exp and log
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 4.2, p. 13 (PDF 14)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators ENNReal

namespace NetUnrelDesign.Main

/-- **Lemma 4.2 (A near-cut list and its derivatives).** Under the standing data of §4 — an instance
satisfying (1.1), `0 < ε ≤ 1/2`, a value `λ₀` passing the branch test (5.8), and
`Q₀ = X ∩ {λ ≥ λ₀ − B}` — there are one program (no oracle) and one constant `C` such that at every
`x ∈ Q₀`, for every `0 < p ≤ 1/2`, the program, given the graph, `q⁰`, `x`, `ε`, `λ₀` and `p`:
on every halting run returns a nonempty duplicate-free list `H_x` of cuts, the value `log h_x(x)`
and all `m` coordinates of `∇ log h_x(x)`, where `h_x(y) = Σ_{C ∈ H_x} e^{−w_y(C)}`, and `h_x` is
positive with `h_x(y) ≤ z(y)` for all `y`; with probability at least `1 − p` it halts with a list
containing every cut of weight at most `αλ(x)`; on that event (4.6)
`(1 − τ)u(x) ≤ h_x(x) ≤ (1 + τ)u(x)`; and its expected cost is at most
`C m²[σ⁻² log(2m) + σ⁻¹ log²(2m/(pσ))]` (4.5), with `α, σ, τ` from (4.3).
Sun 2026, p. 13 (PDF 14). -/
theorem lemma_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ {n m k : ℕ} (I : Instance n m k), I.Standing →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ lam0 : ℝ, BranchHolds n ε lam0 →
          ∀ x ∈ regionQ0 I lam0, ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
            (OnEveryHalt P noOracleFn
                (initState noOracle (graphInts I.ends)
                  ([ε, lam0, p] ++ vecList I.q0 ++ vecList x))
                fun s =>
                  outCutList s n ≠ [] ∧ (∀ c ∈ outCutList s n, c ∈ cuts n) ∧
                  (outCutList s n).Nodup ∧
                  outReal s 0 = Real.log (frozenSum I.ends I.q0 (outCutList s n) x) ∧
                  (∀ e : Fin m, outReal s (1 + e) =
                    fderiv ℝ (fun y => Real.log (frozenSum I.ends I.q0 (outCutList s n) y)) x
                      (Pi.single e 1)) ∧
                  ∀ y : Fin m → ℝ, 0 < frozenSum I.ends I.q0 (outCutList s n) y ∧
                    frozenSum I.ends I.q0 (outCutList s n) y ≤ I.z y) ∧
            failureProb P noOracleFn
                (initState noOracle (graphInts I.ends)
                  ([ε, lam0, p] ++ vecList I.q0 ++ vecList x))
                (fun s => ∀ c ∈ cuts n,
                  cutWeight I.ends (weightAt I.q0 x) c ≤ alphaPar n ε lam0 * I.lam x →
                    c ∈ outCutList s n) ≤ ENNReal.ofReal p ∧
            OnEveryHalt P noOracleFn
                (initState noOracle (graphInts I.ends)
                  ([ε, lam0, p] ++ vecList I.q0 ++ vecList x))
                (fun s => (∀ c ∈ cuts n,
                  cutWeight I.ends (weightAt I.q0 x) c ≤ alphaPar n ε lam0 * I.lam x →
                    c ∈ outCutList s n) →
                  (1 - tauPar ε) * I.u x ≤ frozenSum I.ends I.q0 (outCutList s n) x ∧
                  frozenSum I.ends I.q0 (outCutList s n) x ≤ (1 + tauPar ε) * I.u x) ∧
            expectedWork P noOracleFn
                (initState noOracle (graphInts I.ends)
                  ([ε, lam0, p] ++ vecList I.q0 ++ vecList x)) ≤
              ENNReal.ofReal (C * (m : ℝ) ^ 2 *
                ((sigmaPar n ε lam0)⁻¹ ^ 2 * Real.log (2 * m) +
                  (sigmaPar n ε lam0)⁻¹ *
                    Real.log (2 * m / (p * sigmaPar n ε lam0)) ^ 2)) := by sorry

end NetUnrelDesign.Main
