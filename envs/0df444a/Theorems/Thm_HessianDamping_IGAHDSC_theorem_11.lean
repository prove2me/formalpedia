-- Prove2me | Theorems.Thm_HessianDamping_IGAHDSC_theorem_11
-- name    : HessianDamping.IGAHDSC.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:02.889838+00:00
-- url     : https://prove2.me/theorems/c221878b-635a-4dec-8bed-089c76dfba68
-- title:
--   Theorem 11, p. 29 — linear convergence of IGAHD-SC
-- statement:
--   Let $f:H\to\mathbb R$ be continuously differentiable and $\mu$-strongly convex for $\mu>0$, with an $L$-Lipschitz gradient and minimizer $x^*$. Let $s>0$, $0\le\beta\le1/\sqrt\mu$, and suppose
--   $$8\beta L\le\sqrt\mu,\qquad L\le\frac{\sqrt\mu/(2s)+\mu/\sqrt s}{2\beta\mu+1/\sqrt s+\sqrt\mu/2}.\tag{26}$$
--   For any IGAHD-SC run, set $q=(1+\frac12\sqrt{\mu s})^{-1}$ and $\theta=(1+\sqrt{\mu s})^{-1}$. As $k\to\infty$,
--   $$\|x_k-x^*\|=O(q^{k/2}),\qquad f(x_k)-f(x^*)=O(q^k),$$
--   and
--   $$\theta^k\sum_{j=0}^{k-2}\theta^{-j}\|\nabla f(x_j)\|^2=O(q^k).$$
--
--   These are the paper's geometric rates for iterates, values, and its discounted squared-gradient sum. **Formalization Note** $x^*$ is given with its minimizer property, representing the nonempty minimizer set. Lean writes $q^{k/2}$ as $(\sqrt q)^k$. The paper's summation limit uses $p$ while the summand uses $j$; both are read as $j$. The proof uses $0\le\beta$, so it is explicit, and $8\beta L\le\sqrt\mu$ gives the intended meaning of the first bound in (26) when $\beta=0$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 29, Theorem 11; p. 28, (IGAHD-SC); p. 31, implicit β ≥ 0

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

namespace HessianDamping.IGAHDSC

/-- Theorem 11, p. 29: linear convergence of the IGAHD-SC iterates, values, and discounted gradients. -/
theorem theorem_11 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u w : H, ‖gradient f u - gradient f w‖ ≤ L * ‖u - w‖)
    (xstar : H) (hxstar : ∀ y : H, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / Real.sqrt μ)
    (hL1 : 8 * β * L ≤ Real.sqrt μ)
    (hL2 : L ≤ (Real.sqrt μ / (2 * s) + μ / Real.sqrt s) /
      (2 * β * μ + 1 / Real.sqrt s + Real.sqrt μ / 2))
    (x : ℕ → H) (hrun : IsIGAHDSCRun f μ β s x) :
    (fun k : ℕ => ‖x k - xstar‖) =O[Filter.atTop]
        (fun k : ℕ => Real.sqrt (HessianDamping.IPAHDSC.qRate μ s) ^ k) ∧
      (fun k : ℕ => f (x k) - f xstar) =O[Filter.atTop]
        (fun k : ℕ => HessianDamping.IPAHDSC.qRate μ s ^ k) ∧
      (fun k : ℕ => HessianDamping.IPAHDSC.thetaRate μ s ^ k *
        ∑ j ∈ Finset.range (k - 1),
          (1 / HessianDamping.IPAHDSC.thetaRate μ s) ^ j * ‖gradient f (x j)‖ ^ 2) =O[Filter.atTop]
        (fun k : ℕ => HessianDamping.IPAHDSC.qRate μ s ^ k) := by sorry

end HessianDamping.IGAHDSC
