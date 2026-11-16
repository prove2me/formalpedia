-- Prove2me | Theorems.Thm_KoanaKPaths_Main_Supplement_set_packing_counting
-- name    : KoanaKPaths.Main.Supplement.set_packing_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:31:50.655195+00:00
-- url     : https://prove2.me/theorems/536b8def-f4e2-4e4e-af2d-b5180358656a
-- title:
--   Theorem 3 (companion theorem; not used in the proof of the goal) — approximate counting of set packings
-- statement:
--   Let $d,k\ge1$ and let $E=(E_0,\ldots,E_{m-1})$ be an explicitly given family of $m\ge k$ distinct $d$-element sets. Write $N=\operatorname{packingCount}(E,k)$ for the number of unordered $k$-element pairwise-disjoint subfamilies. For every real $0<\varepsilon,\delta<1$, a single uniform randomized algorithm returns a rational $\widehat N$ satisfying
--   $$
--   \Pr\bigl[|\widehat N-N|\le\varepsilon N\bigr]\ge1-\delta
--   $$
--   in $O^*(2^{dk}\varepsilon^{-2}\log(1/\delta))$ bit time, with the inherited rounded confidence convention described below. Zero counts are included: the success event then requires an exactly zero estimate. Neither $d$ nor $k$ is fixed, and there is no promise of a packing.
--
--   More explicitly, there are circuit and packing machines $A,M$ and positive constants $K,c,K_0,c_0$, fixed before all data. Put $L=|\operatorname{familyCode}(E)|$, $a=\operatorname{ctrl}(\varepsilon)$, $b=\operatorname{ctrl}(\delta)$ and
--   $$
--   B=K\,2^{dk}(1+dk+L)^c4^a(b+1).
--   $$
--   For every fair-bit tape length $T>B$, on every tape both machines halt within $B$ bit steps using at most $B$ tape bits and write the same fraction with positive denominator: $A$ takes the compiled circuit input and $M$ takes the family input. The probability bound concerns this same fraction and these same bounded executions. The composition relation additionally bounds deterministic prefix work by a polynomial in $dk,L$, control copying by its binary length, and simulation of $A$ by constant slowdown.
--
--   The statement includes uniform polynomial-bit computation of the compiler and, for every valid family, well-formedness, homogeneity and coefficient-one at every gate, output degree $dk$, the exact identity
--   $$
--   N\bigl(\operatorname{packingCircuit}(E,k)\bigr)=\operatorname{packingCount}(E,k),
--   $$
--   and gate bound $1+mk(d+1)$ and encoded-length bound $K_0(1+dk+L)^{c_0}$. These are conclusions, not hypotheses. The gate numeral is a direct bound for the implementation of the recurrence in the proof on printed p.10 (PDF p.11): each of at most $mk$ positive-degree states adds $d$ right-product gates and at most one addition, beyond a shared constant-one gate. This result adds the paper's set-packing application as a companion theorem to the path-counting goal; its existing reduction target is Theorem 2.
--
--   **Formalization Note** Every label length and output bit is charged by the published finite-stack model. No oracle or tolerance control occurs in the polynomial size factor. The source supplies no numerical constant for that polynomial, so constants and degrees are existential and uniform. The published ceiling controls satisfy $4^a<4\varepsilon^{-2}$ and $b+1=O(1+\log(1/\delta))$ on the whole interval; for $\delta\le1/2$, $b+1\le3\log_2(1/\delta)$. This is the base mission's declared rounding reading of the printed logarithm, while accuracy covers all real $0<\delta<1$.
--
--   Differences from the source:
--   - encoding: a family of distinct d-element sets and its k-element disjoint subfamilies → a duplicate-free list of finite sets of natural labels and unordered index subsets; reason: injective numbering of the finite ground union and ordering of the family preserve every source instance and packing
--   - encoding: the Section 4.2 circuit construction and application of Theorem 2 → an actual shared-gate compiler, its validity/count/size/bit-computability conclusions and a constant-slowdown composition with a circuit machine; reason: records the source construction with charged deterministic preprocessing and identical rational outputs on the same fair-bit tape; no proven fact is assumed as input
--   - encoding: uniform randomized O*(2^(dk) epsilon^(-2) log(1/delta)) time → positive universal natural constants and degrees before every input, finite fair-bit runs and rational output with explicit timeBudget at degree d*k; reason: makes uniform bit time, random-bit use, input-label lengths and every source tolerance explicit
--   - reading: log(1/delta) for every real 0<delta<1 → the published rounded confidence factor ctrl(delta)+1, hence O(1+log(1/delta)) throughout the full accuracy domain; reason: inherits the base operational convention near delta=1; for delta<=1/2 it is at most 3 log_2(1/delta), and accuracy is never restricted
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 3 (PDF p. 4), Theorem 3; repeated and proved p. 10 (PDF p. 11), Section 4.2; inherited bit-time analysis p. 9 (PDF p. 10), Section 3.2

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_KoanaKPaths_Main_Circuits
import Definitions.Def_KoanaKPaths_Main_Inputs
import Definitions.Def_KoanaKPaths_Main_Supplement_Packings
import Definitions.Def_KoanaKPaths_Main_Supplement_Reduction

open HypergraphUnreliability.FPRAS

namespace KoanaKPaths.Main.Supplement

/-- Theorem 3, printed pp.3,10 / PDF pp.4,11. A companion theorem to the published path goal.
The compiler and both machines are uniform. Compiler validity, the exact count correspondence,
and polynomial bit cost are conclusions, as are total bounded rational output and multiplicative
accuracy. The circuit machine and composite machine write the same fraction on the same tape.
The confidence ceiling convention is inherited from the published circuit interface. -/
theorem set_packing_counting :
    ∃ (A M : CoinMachine) (K c Kpre cpre : ℕ),
      0 < K ∧ 0 < c ∧ 0 < Kpre ∧ 0 < cpre ∧
      CompilesThenRuns M A Kpre cpre ∧
      PolyComputesIn
        (fun x : ℕ × ℕ × List (Finset ℕ) => ValidFamily x.2.2 x.1 x.2.1)
        (fun x => packingData x.2.2 x.1 x.2.1)
        (fun x => circuitCode (packingCircuit x.2.2 x.2.1))
        (fun x => 1 + x.1 * x.2.1 + (familyCode x.2.2).length) ∧
      ∀ (E : List (Finset ℕ)) (d k : ℕ), ValidFamily E d k →
        (packingCircuit E k).IsHomZeroOne (d * k) ∧
        numMultilinear (packingCircuit E k).outputPoly = (packingCount E k : ℤ) ∧
        (packingCircuit E k).gates.length ≤ 1 + E.length * k * (d + 1) ∧
        (circuitCode (packingCircuit E k)).length ≤ Kpre * (1 + d * k + (familyCode E).length) ^ cpre ∧
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ T : ℕ, timeBudget K c (d * k) (familyCode E).length (ctrl ε) (ctrl δ) < T →
          (∀ ω : Fin T → Bool, ∃ Nhat : Frac, 0 < Nhat.den ∧
            M.RunsWithin (packingInput E d k ε δ) (tapeList ω)
              (timeBudget K c (d * k) (familyCode E).length (ctrl ε) (ctrl δ)) (fracCode Nhat) ∧
            A.RunsWithin (circuitInput (packingCircuit E k) ε δ) (tapeList ω)
              (timeBudget K c (d * k) (familyCode E).length (ctrl ε) (ctrl δ)) (fracCode Nhat)) ∧
          1 - δ ≤ fairProb T (fun ω => ∃ Nhat : Frac, 0 < Nhat.den ∧
            M.RunsWithin (packingInput E d k ε δ) (tapeList ω)
              (timeBudget K c (d * k) (familyCode E).length (ctrl ε) (ctrl δ)) (fracCode Nhat) ∧
            A.RunsWithin (circuitInput (packingCircuit E k) ε δ) (tapeList ω)
              (timeBudget K c (d * k) (familyCode E).length (ctrl ε) (ctrl δ)) (fracCode Nhat) ∧
            |((Nhat.val : ℚ) : ℝ) - (packingCount E k : ℝ)| ≤ ε * (packingCount E k : ℝ)) := by sorry

end KoanaKPaths.Main.Supplement
