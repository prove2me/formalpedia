-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_theorem_B_1
-- name    : GaussPolyReg.Approx.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:38.346257+00:00
-- url     : https://prove2.me/theorems/a2725474-80eb-4525-95f6-5f4f061defff
-- title:
--   Theorem B.1 — fourth moment theorem and flattening criterion
-- statement:
--   Fix positive degrees $d_1,\ldots,d_k$. Let $p_{n,i}\in H_{d_i}(X_1,\ldots,X_n)$ and suppose $\mathbb E p_{n,i}p_{n,j}\to C_{ij}$. Write $P_{n,i}$ for their symmetric Hermite coefficient tensors. The following four conditions are equivalent:
--
--   1. $P_n\Rightarrow N(0,C)$.
--   2. $\mathbb E p_{n,i}^4\to3C_{ii}^2$ for every $i$.
--   3. $\|P_{n,i}\otimes_r P_{n,i}\|_F\to0$ for every $i$ and $0<r<d_i$.
--   4. $\|P_{n,i}^{(r)}\|_{\rm op}\to0$ for every $i$ and $0<r<d_i$.
--
--   $$\text{(1)}\iff\text{(2)}\iff\text{(3)}\iff\text{(4)}.$$
--
--   The covariance is allowed to be singular. Positive semidefiniteness follows from covariance convergence and is not assumed. This identifies asymptotically Gaussian chaos vectors by either moment or tensor criteria.
--
--   Differences from the source:
--   - encoding: functions of the original Gaussian variables, with the closed spans fixed in §2 → L² almost-everywhere classes on the product Gaussian space indexed by ℕ; index n uses coordinates 0 through n−1; reason: reindexing X₁,X₂,… changes no random variable or closed-span instance
--   - encoding: four equivalent conditions with limit N(0,C) → List.TFAE and Mathlib multivariateGaussian 0 C, with every convergence along atTop; reason: TFAE asserts all pairwise equivalences; the covariance hypothesis forces C positive semidefinite, so the Gaussian constructor is used on its intended domain
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Theorem B.1, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem theorem_B_1 (k : ℕ) (d : Fin k → ℕ) (hd : ∀ a, 1 ≤ d a)
    (p : ℕ → Fin k → Original) (hp : ∀ n a, p n a ∈ finiteChaos n (d a))
    (C : Matrix (Fin k) (Fin k) ℝ)
    (hC : ∀ a b, Tendsto (fun n => pairing (p n a) (p n b)) atTop (𝓝 (C a b))) :
    List.TFAE [
      TendstoInDistribution (fun n => vectorOf (fun a x => p n a x)) atTop
        id (fun _ => gaussianProduct ℕ) (multivariateGaussian 0 C),
      ∀ a, Tendsto (fun n => ∫ x, (p n a x) ^ 4 ∂gaussianProduct ℕ)
        atTop (𝓝 (3 * (C a a) ^ 2)),
      ∀ a r, 0 < r → r < d a → Tendsto
        (fun n => frobenius (contraction (coefficientTensor (n := n) (d := d a) (p n a)) r))
        atTop (𝓝 0),
      ∀ a r, 0 < r → r < d a → Tendsto
        (fun n => flattenNorm (coefficientTensor (n := n) (d := d a) (p n a)) r)
        atTop (𝓝 0)] := by sorry

end GaussPolyReg.Approx
