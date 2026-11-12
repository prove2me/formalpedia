-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_2_5
-- name    : NetUnrelEst.Main.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:29.088636+00:00
-- url     : https://prove2.me/theorems/8245fd15-b700-4e2d-81b0-bc1206e498a8
-- title:
--   Lemma 2.5 — the preparation: an unbiased estimate Z ∈ [0, 2] with E[Z²; estimate] ≤ Cu², or recursion with λ ≤ d ≤ c₀ log n
-- statement:
--   On the reduced input (a connected graph with $n$ vertices and $s$ edges, no loops or parallel edges, $0<p_e<1$, $n\ge n_0$), let $H=\log(8n)$, $c_0=29/10$, $w_e=-\log p_e$ and $\lambda$ the minimum cut. A randomized procedure runs in expected time $O((s+n)H^2)$ and either returns an estimate $Z\in[0,2]$, or returns a cut of capacity $d$ and chooses recursion. For every outcome of the preparation that chooses an estimate, $Z$ has conditional mean $u$, and
--   $$\mathbb E\big[Z^2;\ \text{an estimate is returned}\big]\le Cu^2.$$
--   Whenever recursion is chosen,
--   $$\lambda\le d\le c_0\log n,\qquad u\ge n^{-c_0}.\tag{12}$$
--   The probability of choosing recursion with $d\ne\lambda$ is at most $n^{-80}$.
--
--   The preparation decides between direct estimation by cut sampling (for large minimum cuts) and the recursion (for small ones). It supplies the recursion with an exact minimum-cut value except with polynomially small probability.
--
--   **Formalization Note.** The procedure is a pair of programs on the extended machine. The preparation $P_1$ runs on the input: integer output $0$ is $1$ for an estimate and $0$ for recursion, integer outputs $1,\dots,n$ give the shore of the returned cut, and real output $0$ is $d$, its capacity. The estimate program $P_2$ is run from $P_1$'s halted state on fresh tape coordinates, and its real output $0$ is $Z$ ($0$ on a non-halting run). The expected time is $\mathbb E[\text{work}(P_1)]$ plus the expected work of $P_2$ on the preparations that choose an estimate. $\mathbb E[Z^2;\cdot]$ is a lintegral. $C$, $n_0$ and $c_w$ are universal.
--
--   Differences from the source:
--   - encoding: one randomized procedure whose preparation outcome is conditioned on → two programs: the preparation P₁, and the estimate P₂ run from P₁'s halted state with a fresh tape; 'every outcome of the preparation' is every halting tape of P₁; reason: running P₂ after P₁ is one procedure, and the split makes the conditional mean given the preparation a statement about P₂'s run
--   - reading: a randomized algorithm with an expected-time bound (no machine named) → an admissible program of the published randomized real RAM extended by capped word instructions, for every word size W ≥ c_w⌈log₂(n + s + 2)⌉ given in the input; reason: the paper uses machine words (App. G.3.2, Corollary G.5) on a unit-cost randomized RAM; the existential is over one program fixed before the input
--   - encoding: O((s + n)H²), C, and 'a sufficiently large absolute constant n₀' (§2.1) → ∃ explicit constants quantified before every input; reason: the meaning of O(·) and of 'there are constants'; the constants are uniform over all inputs
--   - encoding: 'returns a cut of capacity d' → integer outputs 1..n give a nonempty proper shore S, and real output 0 equals w(s(S, Sᶜ)) = Σ_{e crosses} −log p_e; reason: the output layout of a cut and its capacity
--   - encoding: E[Z²; an estimate is returned] and Pr(recursion with d ≠ λ) → a lintegral of ofReal(Z²) over the preparations choosing an estimate, and the tape measure of {P₁ halts, chooses recursion, d ≠ λ}; reason: no integrability side conditions; same quantities
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), pp. 11–12, Lemma 2.5

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelEst_Main_CutSums
import Definitions.Def_NetUnrelEst_Main_WordMachine

open scoped BigOperators ENNReal Classical

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma 2.5.** There are constants `C > 0`, `n₀`, `c_w` and two admissible programs, a
preparation `P₁` and an estimate `P₂` (run after `P₁` from its halted state on a fresh tape), such
that on every reduced input with `n ≥ n₀` and every word size `W ≥ c_w ⌈log₂(n + s + 2)⌉`:
the expected time is at most `C (s + n) H²`; every halting preparation either chooses an estimate
(integer output `0` is `1`) or returns a cut (shore indicators in integer outputs `1, …, n`) of
capacity `d` (real output `0`) and chooses recursion (integer output `0` is `0`); for every
preparation outcome that chooses an estimate, `Z ∈ [0, 2]` on every halting run and `Z` has
conditional mean `u`; `E[Z²; an estimate is returned] ≤ Cu²`; whenever recursion is chosen,
`λ ≤ d ≤ c₀ log n` and `u ≥ n^{−c₀}`, `c₀ = 29/10` (12); and recursion with `d ≠ λ` is chosen with
probability at most `n^{−80}`. Sun 2027, pp. 11–12, Lemma 2.5. -/
theorem lemma_2_5 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ cw : ℕ, ∃ P₁ P₂ : WProgram, WAdmissible P₁ ∧ WAdmissible P₂ ∧
      ∀ {n s : ℕ} (ends : Ends n s) (p : Fin s → ℝ), IsReduced ends p → n₀ ≤ n →
        ∀ W : ℕ, cw * Nat.clog 2 (n + s + 2) ≤ W →
          ∫⁻ ω₁, (wTotalWork W P₁ (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁ +
              if wHalts W P₁ (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁ ∧
                  outInt (wFinalState W P₁
                    (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁) 0 = 1
              then wExpectedWork W P₂ (resume (wFinalState W P₁
                    (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁))
              else 0) ∂jointLaw ≤
            ENNReal.ofReal (C * ((s : ℝ) + n) * Real.log (8 * n) ^ 2) ∧
          wOnEveryHalt W P₁ (initState noOracle (graphInts W ends) (List.ofFn p))
            (fun st => outInt st 0 = 1 ∨
              (outInt st 0 = 0 ∧
                (Finset.univ.filter fun v : Fin n => outInt st (1 + v.val) = 1).Nonempty ∧
                (Finset.univ.filter fun v : Fin n => outInt st (1 + v.val) = 1) ≠ Finset.univ ∧
                outReal st 0 = cutWeight ends (wOf p)
                  (cutOfShore (Finset.univ.filter fun v : Fin n => outInt st (1 + v.val) = 1)) ∧
                lam ends p ≤ outReal st 0 ∧ outReal st 0 ≤ 29 / 10 * Real.log n ∧
                (n : ℝ) ^ (-(29 / 10 : ℝ)) ≤ unrel ends p)) ∧
          (∀ ω₁, wHalts W P₁ (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁ →
            outInt (wFinalState W P₁
              (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁) 0 = 1 →
            wOnEveryHalt W P₂ (resume (wFinalState W P₁
                (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁))
              (fun st => 0 ≤ outReal st 0 ∧ outReal st 0 ≤ 2) ∧
            MeasureTheory.Integrable (wOutput W P₂ (resume (wFinalState W P₁
                (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁))) jointLaw ∧
            ∫ ω₂, wOutput W P₂ (resume (wFinalState W P₁
                (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁)) ω₂ ∂jointLaw =
              unrel ends p) ∧
          ∫⁻ ω₁, (if wHalts W P₁ (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁ ∧
                  outInt (wFinalState W P₁
                    (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁) 0 = 1
              then ∫⁻ ω₂, ENNReal.ofReal (wOutput W P₂ (resume (wFinalState W P₁
                    (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁)) ω₂ ^ 2) ∂jointLaw
              else 0) ∂jointLaw ≤
            ENNReal.ofReal (C * unrel ends p ^ 2) ∧
          jointLaw {ω₁ | wHalts W P₁ (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁ ∧
              outInt (wFinalState W P₁
                (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁) 0 = 0 ∧
              outReal (wFinalState W P₁
                (initState noOracle (graphInts W ends) (List.ofFn p)) ω₁) 0 ≠ lam ends p} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-(80 : ℝ))) := by sorry

end NetUnrelEst.Main
