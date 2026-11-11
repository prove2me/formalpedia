-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_lemma_3_5
-- name    : HamSimTradeoff.AncillaDepth.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:01.571285+00:00
-- url     : https://prove2.me/theorems/1d919360-89c5-4340-bc80-ec8db1062921
-- title:
--   Lemma 3.5 — uniform accuracy controls the scalar response
-- statement:
--   There is an absolute constant $C>0$ with the following property. Fix any architecture, any source hard family with $L\ge2$ and admissible positive weights, and any $\varepsilon\in(0,1/2)$. Suppose its spectral-norm error satisfies
--   $$\|C(t,\delta)-\eta e^{-itA(\delta)}\|\le\varepsilon\quad\text{for every real }\delta\text{ and every real }|t|\le1.$$
--   Then its explicit scalar response obeys
--   $$\sup_{|t|\le1}|g(t)|\le C\varepsilon\bigl(Q+1+\log(1/\varepsilon)\bigr).$$
--   This translates uniform approximation of the hard-family evolution into a bound on the first-order response mismatch. The definition of $g$ remains the independent finite controller sum.
--
--   **Formalization Note** The paper writes $O(\cdot)$; the Lean states an absolute constant $C$ chosen before all parameters, including the weights and $\varepsilon$. The supplied Bernstein reference states the scalar inequality used in the source, with matrix applications obtained through scalar matrix elements.
--
--   Differences from the source:
--   - encoding: O(·) or exp(−O(·)) with an absolute hidden constant → a positive real constant chosen before all other parameters; reason: the proof supplies no numeral; quantifier order enforces uniformity
--   - reading: Q = D/L = Θ(5^{k−1}∑ℓ max_r mℓr) → Q = 5^{k−1}∑ℓ max_r mℓr exactly; reason: this is the displayed representative used by the proof, preserving the asymptotic resource scale
--   - encoding: indices 1,…,L, rounds 1,…,s and branches 1,…,R → zero-based Fin indices, with ancilla |0^a⟩ represented by index zero; reason: a bijective relabeling preserves every matrix product and sum
--   - encoding: L∞ norm on the stated closed interval → sSup of the pointwise complex moduli on that interval; reason: the functions and their iterated derivatives are continuous, so the nonempty compact interval has a finite maximum
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.18, Lemma 3.5 and preceding uniform-error assumption

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- The hypothesis is the hard-family uniform error assumption of p.18. -/
theorem lemma_3_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Architecture) (L : ℕ) (w : HardWeights L) (eps : ℝ),
      0 < eps → eps < 1 / 2 →
      (∀ t delta : ℝ, |t| ≤ 1 →
        ‖hardCompression B w t delta - eta B • evolution (hardA delta) t‖ ≤ eps) →
      intervalNorm (response B) (-1) 1 ≤ C * eps * (depth B + 1 + Real.log (1 / eps)) := by sorry

end HamSimTradeoff.AncillaDepth
