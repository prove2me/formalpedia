-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_lemma_3_1
-- name    : HamSimTradeoff.AncillaDepth.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:25.179193+00:00
-- url     : https://prove2.me/theorems/12170c67-fa29-4a9c-94c5-07b1791435f6
-- title:
--   Lemma 3.1 — Suzuki linear response on the hard family
-- statement:
--   For every integer $k\ge1$, every source hard family with $L\ge2$ and positive weights $\alpha_1=1/2$, $\sum_j\alpha_j=1$, and every real $h$, the Suzuki product formula satisfies
--   $$S_{2k}(h,0)=I,\qquad \partial_\delta S_{2k}(h,0)=-ih\rho_k(h)X.$$
--   For $k\ge2$ its response obeys
--   $$\rho_k(h)=4u_k\rho_{k-1}(u_kh)+(1-4u_k)\rho_{k-1}((1-4u_k)h),\qquad u_k=(4-4^{1/(2k-1)})^{-1}.$$
--   Here $X$, the hard family, and the explicitly defined $\rho_k$ are as above. At $k=1$ the derivative is $-i\sin(h/2)X$, including $h=0$. This statement connects the recursive scalar functions to the actual matrix evolution, rather than defining them by a quotient of matrices.
--
--   **Formalization Note** `HasDerivAt` asserts existence and the specified derivative, for a real variable and complex matrix values. The base case comes from the calculation immediately preceding Lemma 3.1 on the same page.
--
--   Differences from the source:
--   - encoding: indices 1,…,L, rounds 1,…,s and branches 1,…,R → zero-based Fin indices, with ancilla |0^a⟩ represented by index zero; reason: a bijective relabeling preserves every matrix product and sum
--   - encoding: ρ₁(h)=sin(h/2)/h and its Taylor series → ρ₁(0)=1/2 and ρ₁(h)=sin(h/2)/h for h≠0; reason: the Taylor series specifies the removable singularity; ordinary Lean division gives 0 at 0/0
--   - encoding: ρ_k defined as ∂δS_{2k}(h,0)/(−ihX), recursion as the lemma's conclusion → ρ_k defined by the base formula and the displayed recursion, with ∂δS_{2k}(h,0)=−ihρ_k(h)X as the conclusion; reason: the matrix quotient is not a Lean operation; the conjunction says the same thing for every k ≥ 1, h ∈ ℝ
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.15, Lemma 3.1 and its preceding base calculation

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- Lemma 3.1 and its preceding base calculation, p.15. -/
theorem lemma_3_1 (k : ℕ) (hk : 1 ≤ k) {L : ℕ} (w : HardWeights L) (h : ℝ) :
    suzuki k w.alpha (hardH L 0) h = 1 ∧
    HasDerivAt (fun delta : ℝ => suzuki k w.alpha (hardH L delta) h)
      ((-Complex.I * (h : ℂ) * (rho k h : ℂ)) • pauliX) 0 ∧
    (2 ≤ k → rho k h = 4 * u k * rho (k - 1) (u k * h) +
      (1 - 4 * u k) * rho (k - 1) ((1 - 4 * u k) * h)) := by sorry

end HamSimTradeoff.AncillaDepth
