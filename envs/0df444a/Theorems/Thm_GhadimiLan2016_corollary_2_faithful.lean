-- Prove2me | Theorems.Thm_GhadimiLan2016_corollary_2_faithful
-- name    : GhadimiLan2016.corollary_2_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T00:55:37.563982+00:00
-- url     : https://prove2.me/theorems/7f5829b9-7d87-4614-8577-ab1b4ed521a5
-- title:
--   Corollary 2 (Ghadimi–Lan) — the aggressive step-size policy on nonconvex composite problems
-- statement:
--   In the setting of Theorem 2 (problem (1.3), Assumption 2, $x^*$ optimal, $L_\Psi=L_f+L_h>0$), run Algorithm 2 from any $x_0$ with $\alpha_k=\frac{2}{k+1}$, $\beta_k=\frac{1}{2L_\Psi}$, $\lambda_k=\frac{k\beta_k}{2}$. Then for every $N\ge1$ $$\min_{k\le N}\|\mathcal G(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k)\|^2\le 24L_\Psi\Big(\frac{4L_\Psi\|x_0-x^*\|^2}{N^2(N+1)}+\frac{L_f}{N}(\|x^*\|^2+2M^2)\Big),$$ and if $L_f=0$ then $\Phi(x^{ag}_N)-\Phi(x^*)\le\frac{4L_\Psi\|x_0-x^*\|^2}{N(N+1)}$.
--
--   This is Corollary 2 of Ghadimi and Lan, (2.54)–(2.55): the explicit rate of the accelerated gradient method on nonconvex composite problems under its aggressive step-size policy, obtained by specializing Theorem 2.
--
--   **Formalization Note** The hypothesis $L_\Psi>0$ only makes $\beta_k=1/(2L_\Psi)$ well defined.
-- source:
--   Ghadimi & Lan, Accelerated gradient methods for nonconvex nonlinear and stochastic programming, Math. Program. 156 (2016), arXiv:1310.3787, p. 13, Corollary 2, (2.54)–(2.55)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

open ConvexOptAlg.SmoothGD NonconvexAG.Composite

theorem GhadimiLan2016.corollary_2_faithful {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h) (hL : 0 < Lf + Lh)
    (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (x0 : NonconvexAG.Smooth.E n) (M : ℝ) (hA2 : Assumption2 P M)
    (N : ℕ) (hN : 1 ≤ N)
    (xstar : NonconvexAG.Smooth.E n) (hxstar : xstar ∈ K)
    (hopt : ∀ u ∈ K, f xstar + h xstar + X xstar ≤ f u + h u + X u) :
    let α : ℕ → ℝ := fun k => 2 / ((k : ℝ) + 1)
    let β : ℕ → ℝ := fun _ => 1 / (2 * (Lf + Lh))
    let lam : ℕ → ℝ := fun k => (k : ℝ) * β k / 2
    let Φ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x + X x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN)
        (fun k => ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2) ≤
      24 * (Lf + Lh) * (4 * (Lf + Lh) * ‖x0 - xstar‖ ^ 2 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1)) +
        Lf / (N : ℝ) * (‖xstar‖ ^ 2 + 2 * M ^ 2)) ∧
    (Lf = 0 → Φ (xag N) - Φ xstar ≤ 4 * (Lf + Lh) * ‖x0 - xstar‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))) := by sorry
