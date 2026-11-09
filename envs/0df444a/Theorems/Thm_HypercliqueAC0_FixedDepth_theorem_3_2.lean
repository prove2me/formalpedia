-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_theorem_3_2
-- name    : HypercliqueAC0.FixedDepth.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:12:14.658193+00:00
-- url     : https://prove2.me/theorems/c02bdb96-a5fb-4dcf-82f9-e3477245c821
-- title:
--   Theorem 3.2: Tal’s uniform Fourier tail bound
-- statement:
--   Fix an integer $h\ge1$. There is a real $K>0$, depending only on $h$, such that the following holds for every finite variable set $X$, every Boolean function $f$, every real $\sigma\ge2$, and every circuit $C$ of depth at most $h$ with at most $\sigma$ gates computing $f$. For every real $D\ge0$,
--
--   $$\sum_{|S|\ge D}\widehat f(S)^2\le2\cdot2^{-D/[K(\log_2\sigma)^{h-1}]}.$$
--
--   This is the cited uniform Fourier tail estimate used to obtain the biased estimate.
--
--   **Formalization Note** The coefficient is evaluated at bias $1/2$. The constant is selected before the variable set, the function, the circuit, its gate budget and the degree threshold.
--
--   Differences from the source:
--   - encoding: Boolean-cube Fourier coefficients and product-measure probabilities → Boolean functions converted to real indicators and finite weighted sums over all assignments; reason: the finite product distribution and every coefficient have the same values
--   - encoding: $O_h((\log\sigma)^{h-1})$ → a positive constant $K$ depending only on $h$ times $(\log_2\sigma)^{h-1}$; reason: makes the printed uniform dependence explicit
--   - encoding: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: pruning unused gates and deleting repeated sources preserve output and depth and cannot increase gate count
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.12 (PDF p.14), Theorem 3.2, citing [Tal17, Theorem 18]

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Theorem 3.2, p.12 (PDF 14), citing Tal17, Theorem 18. K depends only on h. -/
theorem theorem_3_2 (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : Type) [Fintype X] (f : (X → Bool) → Bool)
      (σ : ℝ) (C : MantriCVQ.ACCircuit X),
      2 ≤ σ → C.depth ≤ h → (C.gates.length : ℝ) ≤ σ → (∀ x, C.eval x = f x) →
      ∀ D : ℝ, 0 ≤ D →
        fourierTailGE (1 / 2) (boolReal f) D ≤
          2 * (2 : ℝ) ^ (-D / (K * (Real.logb 2 σ) ^ (h - 1))) := by sorry

end HypercliqueAC0.FixedDepth
