-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_gaussian_permanent_exact_density
-- name    : GinibrePermanent977.Anticoncentration.gaussian_permanent_exact_density
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:13:12.583893+00:00
-- url     : https://prove2.me/theorems/360348a9-84ff-4494-a489-ad169168673d
-- title:
--   Exact radial density and small-ball bounds for Gaussian permanents
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$, let $\beta$ be its real dimension, and let $G_n$ have independent standard $\mathbb K$-Gaussian entries. For $n\ge1$, put $W_n=\operatorname{per}_{\mathbb K}(G_n)/\sqrt{n!}$, where quaternionic products follow increasing row order. There is a measurable radial Lebesgue density $p_n$ of $W_n$ such that
--
--   $$
--   \operatorname*{ess\,sup}p_n=p_n(0),\qquad p_n(z)\le p_n(0)\le\kappa_{n,\beta}\quad(z\in\mathbb K).
--   $$
--
--   For every $\varepsilon>0$ and every center $z\in\mathbb K$,
--
--   $$
--   \mathbb P\bigl(|W_n-z|\le\varepsilon\bigr)\le\min\{1,\omega_\beta\kappa_{n,\beta}\varepsilon^\beta\}.
--   $$
--
--   Here $\kappa_{n,\beta}$ is the closed-form constant of equation (22), and $\omega_\beta$ is the volume of the unit ball of $\mathbb R^\beta$. These are the exact density and small-ball estimates used with Lemma 3.8 to obtain the polynomial bounds of Theorem 1.1.
-- source:
--   Koehler and Leung, Anticoncentration of the Permanent in Ginibre Ensembles, STOC 2027 submission #977, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/977.pdf, p.13, proof of Theorem 1.1, equations (25)–(28); p.12 equation (22).

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open GinibrePermanent977.Anticoncentration
open scoped ENNReal Nat

theorem GinibrePermanent977.Anticoncentration.gaussian_permanent_exact_density
    (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : F.K → ℝ≥0∞,
      Measurable p ∧
      (∀ s : Set F.K, MeasurableSet s →
        ginibre F n n (normPer ⁻¹' s) = ∫⁻ z in s, p z) ∧
      (∀ z w : F.K, ‖z‖ = ‖w‖ → p z = p w) ∧
      essSup p volume = p 0 ∧
      (∀ z : F.K, p z ≤ p 0) ∧
      p 0 ≤ ENNReal.ofReal (kappa F n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ z : F.K,
        ginibre F n n {G | ‖normPer G - z‖ ≤ ε} ≤
          ENNReal.ofReal (min 1 (omegaBall F * kappa F n * ε ^ F.beta)) := by sorry
