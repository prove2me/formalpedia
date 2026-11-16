-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_Supplement_theorem_5
-- name    : HypercliqueCircuits.Circuits.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:14:31.282874+00:00
-- url     : https://prove2.me/theorems/88b906ef-f645-442e-ba8e-afc9c4b61bcd
-- title:
--   Theorem 5 — nontrivial k-term progression detection
-- statement:
--   There are universal constants $a,b>0$ and a positive sequence $\varepsilon_k$, for every $k\ge4$, satisfying
--
--   $$a2^k\le\log_2(1/\varepsilon_k)\le b2^k.$$
--
--   For each fixed $k\ge4$ there are an algorithm and $C_k>0$ which, for every $n\ge1$ and $A\subseteq\{0,\ldots,n\}$, decide whether $A$ contains a nontrivial $k$-term arithmetic progression within
--
--   $$T(A)\le C_k n^{2-2\varepsilon_k/k}.$$
--
--   A nontrivial progression has positive integer step, and the output is 1 exactly when one exists and 0 otherwise. The constants $a,b$ are fixed before $k$, while the program and $C_k$ may depend on $k$ only. No asymptotic slack is added to the displayed exponent. This retains both the dependence $2\varepsilon_k/k$ and the two-sided doubly exponential class from Theorem 1.
--
--   Differences from the source:
--   - reading: algorithmic running time without an explicit instruction set → a finite Program Empty with actual halting execution and the published executionBits cost; reason: the supplement inherits the live mission machine; arithmetic, accessed-word lengths, and output serialization are charged, and no oracle instruction can be instantiated
--   - reading: ε_k in Theorem 1 is specified only up to 2^(−Θ(2^k)); the proof of Theorem 5 drops the o(1) term of Theorem 2 → one existential positive sequence ε with universal two-sided log₂ bounds and the exact exponent 2−2ε_k/k; reason: the brief requires the existential Θ-class reading: taking saving k/2 absorbs positive slack while staying in the same class, and pointwise minima allow a common saving for circuit construction and AP detection
--   - encoding: A is a subset of {0,…,n} containing a nontrivial k-term AP → A is a finite subset of Fin (n+1), with positive natural step and input n followed by n+1 indicator words; the output is a single correct decision word; reason: both endpoints are included and every increasing nontrivial integral AP has this representation
--   - encoding: asymptotic running time in the input size → an explicit positive multiplicative constant and a bound for every n at least 1; reason: finitely many smaller positive sizes are absorbed into the constant; n=0 is outside the power-bound convention
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, p.2, Theorem 5 (PDF 3); proof p.26 (PDF 27)

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Progression

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- Theorem 5, printed p.2 (proof p.26), PDF p.3 (proof p.27).
Reading: epsilon is existential in the source's doubly exponential class.
The proof's omission of o(1) is absorbed by choosing smaller savings within
that SAME class; the exponent here has no asymptotic slack. -/
theorem theorem_5 :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ ε : ℕ → ℝ,
      (∀ k : ℕ, 4 ≤ k → 0 < ε k) ∧
      (∀ k : ℕ, 4 ≤ k →
        a * (2 : ℝ) ^ k ≤ Real.logb 2 (1 / ε k) ∧
        Real.logb 2 (1 / ε k) ≤ b * (2 : ℝ) ^ k) ∧
      ∀ k : ℕ, 4 ≤ k → ∃ prog : Program Empty, ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 0 < n → ∀ A : Finset (Fin (n + 1)), ∃ t : ℕ,
          (execute prog (progressionInput A) t).halted = true ∧
          (execute prog (progressionInput A) t).output = progressionOutput k A ∧
          (executionBits Empty.elim prog (progressionInput A) t : ℝ) ≤
            C * (n : ℝ) ^ (2 - 2 * ε k / (k : ℝ)) := by sorry

end HypercliqueCircuits.Circuits.Supplement
