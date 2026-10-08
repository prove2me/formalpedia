-- Prove2me | Theorems.Thm_OptimalSGD_Suffix_eq_3
-- name    : OptimalSGD.Suffix.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:49.197684+00:00
-- url     : https://prove2.me/theorems/acaeaeee-4bb1-4a02-b47d-61598a24cfcd
-- title:
--   (3) — the summed one-step inequality Σ E⟨g_t, w_t − w*⟩ ≤ Σ η_tG²/2 + Σ (E‖w_t − w*‖² − E‖w_{t+1} − w*‖²)/(2η_t)
-- statement:
--   Under the standing assumptions of the paper — $W\subseteq\mathbb R^d$ closed and convex with $0\in W$, $F$ $\lambda$-strongly convex on $W$ ($\lambda>0$), $g$ a jointly measurable stochastic subgradient oracle for $F$ relative to $W$ with $\mathbb E_z\|g(w,z)\|^2\le G^2$ for all $w\in W$, and $w^*\in W$ a minimizer of $F$ over $W$ — run projected SGD $w_1=0$, $w_{t+1}=\Pi_W(w_t-\eta_t\,g(w_t,z_t))$ with $\eta_t=1/(\lambda t)$ on an i.i.d. sample $z_1,\dots,z_T\sim D$. Write $g_t=\mathbb E_{z\sim D}\,g(w_t,z)$ for the oracle mean at the current iterate. Then every expectation below is finite, and for every integer $0\le k\le T$,
--   $$\sum_{t=k+1}^{T}\mathbb E\big[\langle g_t,w_t-w^*\rangle\big]\ \le\ \sum_{t=k+1}^{T}\frac{\eta_tG^2}{2}+\sum_{t=k+1}^{T}\left(\frac{\mathbb E\|w_t-w^*\|^2}{2\eta_t}-\frac{\mathbb E\|w_{t+1}-w^*\|^2}{2\eta_t}\right).$$
--
--   The paper uses it with $k=(1-\alpha)T$; the suffix parameter $\alpha$ enters only through $k$. It is the starting point of the analysis of the α-suffix average in Theorem 5.
--
--   **Formalization Note** Lean's iterate index is the paper's $t-1$. The first conjunct of the Lean statement asserts that $\|w_t-w^*\|^2$ and $\langle g_t,w_t-w^*\rangle$ are integrable for $t=k+1,\dots,T+1$, so that no Bochner integral in the inequality takes Lean's default value $0$.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 6, eq. (3) (restated as the first summed display of App. B.6, p. 18)

import Definitions.Def_OptimalSGD_Suffix_Model

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

namespace OptimalSGD.Suffix

/-- **(3)** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, §5, p. 6; restated in App. B.6, p. 18).
Under the standing assumptions of §2 and `η_t = 1/(λt)`, for `k ≤ T` and `S ∼ D^T`,
`Σ_{t=k+1}^T E⟨g_t, w_t − w*⟩ ≤ Σ_{t=k+1}^T η_t G²/2
  + Σ_{t=k+1}^T (E‖w_t − w*‖²/(2η_t) − E‖w_{t+1} − w*‖²/(2η_t))`,
where `g_t = E_z g(w_t, z)` is the oracle mean at `w_t`. The paper takes `k = (1 − α)T`.
The first conjunct records that every expectation involved is finite. -/
theorem eq_3
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    (T k : ℕ) (hkT : k ≤ T) :
    (∀ t ∈ Finset.Icc (k + 1) (T + 1),
      Integrable (fun S => ‖sgdStrongIterates lam W g S (t - 1) - wstar‖ ^ 2) (iidLaw D T) ∧
      Integrable (fun S => ⟪oracleMean D g (sgdStrongIterates lam W g S (t - 1)),
        sgdStrongIterates lam W g S (t - 1) - wstar⟫_ℝ) (iidLaw D T)) ∧
    ∑ t ∈ Finset.Icc (k + 1) T,
        ∫ S, ⟪oracleMean D g (sgdStrongIterates lam W g S (t - 1)),
          sgdStrongIterates lam W g S (t - 1) - wstar⟫_ℝ ∂(iidLaw D T) ≤
      ∑ t ∈ Finset.Icc (k + 1) T, (1 / (lam * t)) * G ^ 2 / 2 +
      ∑ t ∈ Finset.Icc (k + 1) T,
        ((∫ S, ‖sgdStrongIterates lam W g S (t - 1) - wstar‖ ^ 2 ∂(iidLaw D T)) /
            (2 * (1 / (lam * t))) -
          (∫ S, ‖sgdStrongIterates lam W g S t - wstar‖ ^ 2 ∂(iidLaw D T)) /
            (2 * (1 / (lam * t)))) := by sorry

end OptimalSGD.Suffix
