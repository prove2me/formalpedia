-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_uStatistic_tendstoInDistribution
-- name    : IntermediateDisorder.PointToLine.uStatistic_tendstoInDistribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:42:15.973203+00:00
-- url     : https://prove2.me/theorems/abfc31f0-2567-4c01-b624-002a8449fa33
-- title:
--   Theorem 4.3 — $n^{-3k/4}\mathcal S_k^n(g)\to I_k(g)$ in law, jointly over finitely many orders
-- statement:
--   Let the environment $\omega$ be i.i.d. with mean zero and variance one, and let $W$ be a white noise on $[0,1]\times\mathbb R$ with multiple stochastic integrals $I=(I_k)$. For every $k$ and $g\in L^2([0,1]^k\times\mathbb R^k)$,
--
--   $$n^{-3k/4}\,\mathcal S_k^n(g)\xrightarrow{(d)}\int_{[0,1]^k}\int_{\mathbb R^k}g(\mathbf t,\mathbf x)\,W^{\otimes k}(d\mathbf t\,d\mathbf x)=I_k(g)\qquad(n\to\infty).$$
--
--   Moreover, for any $k_1,\dots,k_m\in\mathbb N$ and $g_l\in L^2([0,1]^{k_l}\times\mathbb R^{k_l})$, one has the joint convergence in $\mathbb R^m$
--
--   $$\big(n^{-3k_1/4}\mathcal S_{k_1}^n(g_1),\dots,n^{-3k_m/4}\mathcal S_{k_m}^n(g_m)\big)\xrightarrow{(d)}\big(I_{k_1}(g_1),\dots,I_{k_m}(g_m)\big).$$
--
--   This is the paper's main technical theorem: discrete weighted U-statistics in an i.i.d. space–time environment converge to multiple Wiener–Itô integrals of white noise.
--
--   **Formalization Note** $I_k(g)$ for non-symmetric $g$ is $I_k(\operatorname{Sym}g)$, which is what the characterization of $I_k$ by indicators of products of disjoint sets gives; the statement holds as printed in that convention. The limits are on the white-noise space, the prelimit variables on the environment space.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 23, Theorem 4.3

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Definitions.Def_IntermediateDisorder_PointToLine_UStatistic

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory Filter

/-- Theorem 4.3: for `g ∈ L²([0,1]^k × ℝ^k)`, `n^{-3k/4} 𝒮_k^n(g) → I_k(g)` in distribution, and
jointly `(n^{-3k_l/4} 𝒮_{k_l}^n(g_l))_{l ≤ m} → (I_{k_l}(g_l))_{l ≤ m}`. -/
theorem uStatistic_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    (W : Set (ℝ × ℝ) → Ω' → ℝ) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) :
    (∀ (k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)),
      TendstoInDistribution
        (fun (n : ℕ) a => (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) * (uStatistic ω Q n k g : Ω → ℝ) a)
        atTop (I k g : Ω' → ℝ) (fun _ => Q) Q') ∧
    (∀ (m : ℕ) (k : Fin m → ℕ) (g : (l : Fin m) → Lp ℝ 2 (kernelMeasure (k l))),
      TendstoInDistribution
        (fun (n : ℕ) a l => (n : ℝ) ^ (-(3 * (k l : ℝ) / 4)) *
          (uStatistic ω Q n (k l) (g l) : Ω → ℝ) a)
        atTop (fun b l => (I (k l) (g l) : Ω' → ℝ) b) (fun _ => Q) Q') := by sorry

end IntermediateDisorder.PointToLine
