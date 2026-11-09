-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_theorem_5_1
-- name    : HypercliqueAC0.FixedDepth.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:13:31.342363+00:00
-- url     : https://prove2.me/theorems/659cfd36-c9e4-4bd8-b268-6f7d7be1c345
-- title:
--   Theorem 5.1: the explicit fixed-depth hyperclique gate lower bound
-- statement:
--   Fix integers $h,r\ge2$ and reals $\varepsilon,\eta>0$. Define
--
--   $$c_r=\left(1-\frac1r\right)r^{-1/(r-1)}.$$
--
--   There exist natural thresholds $\ell_0,m_0$, depending only on $h,r,\varepsilon,\eta$, such that for every $m\ge m_0$ and every integer $\ell$ satisfying $\ell_0\le\ell\le m^{1/h-\varepsilon}$, every De Morgan circuit of depth at most $h$ computing $\ell\text{-}\mathsf{Clique}^r_m$ satisfies
--
--   $$G(C)>m^{(c_r(h\varepsilon)^{r/(r-1)}-\eta)\ell}.$$
--
--   Here $G(C)$ counts noninput gates. The circuit permits constants, negated input literals, unbounded fan-in and sharing of subcircuits. This is the full explicit lower bound of the paper.
--
--   **Formalization Note** The thresholds precede $m,\ell,C$. No hypotheses $r\le\ell$, $\ell\le m$, $\varepsilon<1/h$ or an upper bound on $\eta$ are added. The range may be empty for large $\varepsilon$, as in the source. The final inequality is strict and uses the gate-list length.
--
--   Differences from the source:
--   - encoding: $[m]=\{1,\ldots,m\}$ and $r$-subsets → $\mathrm{Fin}\,m$ with edge subtype of cardinality $r$; reason: a relabeling bijection preserves the entire hypergraph and all circuit instances
--   - encoding: integer size parameters and thresholds → natural-number parameters and thresholds, with real casts before division and exponentiation; reason: these parameters count vertices, uniformity, depth or lower thresholds; a natural threshold can dominate any integer threshold without changing the source conclusion
--   - encoding: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: pruning unused gates and deleting repeated sources preserve output and depth and cannot increase gate count
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.18 (PDF p.20), Theorem 5.1

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Theorem 5.1, p.18 (PDF 20), at its full printed strength.
The thresholds depend only on h, r, ε and η. No restriction ε < 1/h or ℓ ≥ r is added. -/
theorem theorem_5_1 (h r : ℕ) (hh : 2 ≤ h) (hr : 2 ≤ r)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ ℓ₀ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
      (ℓ : ℝ) ≤ (m : ℝ) ^ (1 / (h : ℝ) - ε) →
      ∀ C : MantriCVQ.ACCircuit (Edge m r), C.depth ≤ h →
        (∀ x, C.eval x = hyperclique m r ℓ x) →
        (m : ℝ) ^ ((c r * ((h : ℝ) * ε) ^ ((r : ℝ) / ((r : ℝ) - 1)) - η) * (ℓ : ℝ)) <
          (C.gates.length : ℝ) := by sorry

end HypercliqueAC0.FixedDepth
