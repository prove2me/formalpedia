-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_theorem_1_4
-- name    : MultiSpinCounting.Positive.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:05.231999+00:00
-- url     : https://prove2.me/theorems/b4ed60dd-ccdf-405a-b32d-91afb9c24b69
-- title:
--   Theorem 1.4 — deterministic FPTAS for positive multi-spin partition functions
-- statement:
--   Fix $q\ge3$, $K\ge1$, $\alpha\ge0$, $D\ge1$ and $c>0$ with $Dc<1$. There exist a positive natural exponent $C$ and one finite deterministic bit machine, depending only on these parameters, such that every positive rational $q$-spin instance $\Phi$ on an $n$-vertex graph, $n\ge1$, satisfying
--   $$\forall\ell\ge0,\quad S_\ell(G)\le Kn^\alpha D^\ell,\qquad \forall e\in E(G),\quad c_B(A_e)\le c,$$
--   and every binary rational $0<\varepsilon<1$ yield a rational output $\widehat Z$ with
--   $$Z(\Phi)\le\widehat Z\le(1+\varepsilon)Z(\Phi)$$
--   within
--   $$\left(\frac{n+|\Phi|+\operatorname{bit}(\varepsilon)}{\varepsilon}\right)^C$$
--   steps. Both lengths are actual serialization lengths; the bound depends on the value of $\varepsilon$ as well as its binary length. The machine and exponent are chosen before the graph, instance and tolerance.
--
--   This states the full deterministic counting guarantee, without placing recursive polytopes or optimization oracles in the goal’s hypotheses.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and spin sets → Fin n and Fin q, with an active vertex subset; reason: relabeling preserves every instance; active subsets implement the source sub-instances and the fixed vertex order
--   - encoding: binary rational data and bit operations → published binary serializers and a finite-stack FinTM2 machine, with time witnessed by TM2OutputsInTime; reason: the encoder only serializes input data; all stacks, control and program labels are finite, and a fixed macro cost is absorbed in the constant
--   - encoding: a graph family satisfying (1.4) → every individual input graph satisfying the same pointwise walk bound; reason: the family of all such graphs satisfies (1.4), and every source family is contained in it; the machine is uniform before all graphs
--   - encoding: a constant real exponent → a positive natural exponent; reason: rounding the exponent upward preserves the bound because its base exceeds one
--   - generalization: an ε-approximation in Theorem 1.4 → the one-sided guarantee Z ≤ Zhat ≤ (1+ε)Z; reason: p. 3 and the proof on p. 17 assert this stronger guarantee, which implies the displayed approximation in Theorem 1.4
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), pp. 3–4, Theorem 1.4; proof pp. 17–18

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Encoding

namespace MultiSpinCounting.Positive
open OnlineCRS.Combine

/-- Theorem 1.4, p. 4, with the stronger one-sided guarantee stated on p. 3.
All parameters precede the machine and exponent, which precede every input. -/
theorem theorem_1_4 (q : ℕ) (hq : 3 ≤ q) (K α D c : ℝ)
    (hK : 1 ≤ K) (hα : 0 ≤ α) (hD : 1 ≤ D) (hc : 0 < c) (hDc : D*c < 1) :
    ∃ (C : ℕ) (M : BitMachine), 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) (Φ : Instance n q ℚ),
        Φ.active = Finset.univ → IsPositive Φ → WalkBound Φ n K α D →
        (∀ e ∈ edges Φ, cB ((realInstance Φ).interaction e.1 e.2) ≤ c) →
        ∀ ε : ℚ, 0 < ε → ε < 1 →
        ∃ (Zhat : ℚ) (m : ℕ),
          (m : ℝ) ≤ (((n : ℝ) + (encInstance Φ).length + (encRat ε).length) / (ε : ℝ)) ^ C ∧
          Runs M (inputEncoding Φ ε) (encRat Zhat) m ∧
          partition (realInstance Φ) ≤ (Zhat : ℝ) ∧
          (Zhat : ℝ) ≤ (1 + (ε : ℝ)) * partition (realInstance Φ) := by sorry

end MultiSpinCounting.Positive
