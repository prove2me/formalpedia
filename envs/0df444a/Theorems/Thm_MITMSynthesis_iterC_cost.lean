-- Prove2me | Theorems.Thm_MITMSynthesis_iterC_cost
-- name    : MITMSynthesis.iterC_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:10:25.571801+00:00
-- url     : https://prove2.me/theorems/39bf296c-3d95-466b-ad7a-e8dfc571ef94
-- title:
--   Iteration $i$ of MITM-factor costs $O(|V_{n,\mathcal G}|^i\log|V_{n,\mathcal G}|^i)$ (corrected: $|V_{n,\mathcal G}|\ge 2$)
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $M$ be a monoid with an adjoint operation and a linear order, and let `vs` be a list of at least two (label, element) pairs. For every target $U$, every depth bound $l$ and every $i \ge 1$, iteration $i$ of MITM-factor, run on the list $S_{i-1}$ built from `vs`, costs at most
--
--   $$
--   C \cdot |vs|^i \cdot \log\bigl(|vs|^i\bigr)
--   $$
--
--   unit-cost steps. When `vs` is a duplicate-free enumeration of $V_{n,\mathcal G}$, $|vs| = |V_{n,\mathcal G}|$ and this is the paper's bound $2|V_{n,\mathcal G}|^i\log(|V_{n,\mathcal G}|^i)$ up to the constant.
--
--   Summing this bound over the iterations gives the running time of the whole algorithm.
--
--   **Formalization Note** The statement is written for iteration $j+1$ run on `buildS vs j`, $j \ge 0$, to avoid natural-number subtraction.
--
--   Differences from the source:
--   - generalization: iteration i of MITM-factor over V_{n,G} ⊆ U(2^n) → iteration i over any list vs of (label, element) pairs in any monoid with an adjoint and a linear order; reason: the costs do not depend on the algebra; taking vs a duplicate-free enumeration of V_{n,G} gives |vs| = |V_{n,G}| and the paper's iteration
--   - reading: time bounded above by 2|V_{n,G}|^i log(|V_{n,G}|^i) → at most C · |vs|^i · log(|vs|^i) unit-cost steps for an absolute constant C; reason: the paper's time units are unspecified, so its factor 2 is read as part of the O-constant
--   - correction: the bound for every V_{n,G} → the bound when |vs| = |V_{n,G}| ≥ 2; reason: counterexample: G = {X} on one qubit gives V_{n,G} = {X}, so 2 · 1^i log(1^i) = 0 while the iteration performs at least one step
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6 ("As |S_i| ≤ |V_{n,G}|^i, the ith iteration thus takes time bounded above by 2|V_{n,G}|^i log(|V_{n,G}|^i)")

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_MITMSynthesis_mitmFactor

namespace MITMSynthesis

/-- **Cost of one iteration.** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, §3, p. 6: "As
|S_i| ≤ |V_{n,G}|^i, the ith iteration thus takes time bounded above by
2|V_{n,G}|^i log(|V_{n,G}|^i)."
There is one absolute constant `C` such that for every list `vs` of at least two (label, element)
pairs, every target `U`, every depth bound `l` and every `i ≥ 1`, iteration `i` of MITM-factor,
run on `S_{i-1} = buildS vs (i - 1)`, costs at most `C · |vs|^i · log(|vs|^i)`. Here iteration
`i = j + 1` is run on `buildS vs j`. -/
theorem iterC_cost :
    ∃ C : ℝ, ∀ (α M : Type) [Monoid M] [Star M] [LinearOrder M] (vs : List (α × M)) (U : M)
      (l j : ℕ), 2 ≤ vs.length →
      ((iterC vs U l (j + 1) (buildS vs j).val).cost : ℝ) ≤
        C * (vs.length : ℝ) ^ (j + 1) * Real.log ((vs.length : ℝ) ^ (j + 1)) := by sorry

end MITMSynthesis
