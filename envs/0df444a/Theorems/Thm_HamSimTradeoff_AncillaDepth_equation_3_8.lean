-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_equation_3_8
-- name    : HamSimTradeoff.AncillaDepth.equation_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:58.294234+00:00
-- url     : https://prove2.me/theorems/049888e2-80e2-4a0a-af67-27fcd60a6415
-- title:
--   Eq. (3.8) — frequency control and iterated Markov bound
-- statement:
--   For every $k\ge1$, there are at most $2^{k-1}$ real sine frequencies $|\nu_j|\le1/2$ and real amplitudes $A_j$ such that
--   $$h\rho_k(h)=\sum_j A_j\sin(\nu_jh)\quad\text{for every real }h.$$
--   For every architecture the scalar response has a representation $g(t)=bt+\sum_{j=1}^M a_je^{i\lambda_jt}$ with $b=i\eta/2$, distinct real $|\lambda_j|\le1/2$, complex coefficients $a_j$, and $M\le2^ks2^a$. There is an absolute constant $C>0$, chosen before the architecture and derivative order, such that for every integer $r\ge1$,
--   $$\|g^{(r)}\|_{[0,1]}\le\exp\bigl(C(rk+r\log(s2^a))\bigr)\|g\|_{[0,1]}.$$
--   The functions are finite analytic sums, so these are their ordinary iterated real derivatives and finite interval norms. This supplies the upper derivative estimate together with its frequency-count premises from the source.
--
--   **Formalization Note** The paper writes $O(\cdot)$ and $e^{O(\cdot)}$; the Lean states an absolute constant $C$ chosen before all parameters. Counting two exponential frequencies per sine gives the exact representation count $2^ks2^a$, a witness to the printed $O(2^ksR)$.
--
--   Differences from the source:
--   - encoding: O(·) or exp(−O(·)) with an absolute hidden constant → a positive real constant chosen before all other parameters; reason: the proof supplies no numeral; quantifier order enforces uniformity
--   - encoding: L∞ norm on the stated closed interval → sSup of the pointwise complex moduli on that interval; reason: the functions and their iterated derivatives are continuous, so the nonempty compact interval has a finite maximum
--   - encoding: M=O(2^kK)=O(2^ksR) after counting at most 2^{k−1}K sine frequencies → M≤2^ksR, with distinct frequencies after combining equal terms; reason: each sine contributes two exponentials and K≤sR; this spells out the stated count
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), pp.18–19, §3.2, frequency-count paragraph and Eq. (3.8)

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- Frequency statements of pp.18–19 and the iterated Markov bound (3.8). -/
theorem equation_3_8 :
    (∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, N ≤ 2 ^ (k - 1) ∧
      ∃ (amp freq : Fin N → ℝ), (∀ j, |freq j| ≤ 1 / 2) ∧
        ∀ h : ℝ, h * rho k h = ∑ j, amp j * Real.sin (freq j * h)) ∧
    (∀ B : Architecture, ∃ M : ℕ, M ≤ 2 ^ B.k * B.s * 2 ^ B.a ∧
      ∃ (a : Fin M → ℂ) (freq : Fin M → ℝ), Function.Injective freq ∧
        (∀ j, |freq j| ≤ 1 / 2) ∧
        ∀ t : ℝ, response B t = exponentialSum (Complex.I * eta B / 2) a freq t) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (B : Architecture) (r : ℕ), 1 ≤ r →
      intervalNorm (iteratedDeriv r (response B)) 0 1 ≤
        Real.exp (C * ((r : ℝ) * B.k + (r : ℝ) * Real.log (B.s * 2 ^ B.a : ℕ))) *
          intervalNorm (response B) 0 1) := by sorry

end HamSimTradeoff.AncillaDepth
