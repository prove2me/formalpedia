-- Prove2me | Theorems.Thm_Hairer_testFunction_decomposition_scaledTest
-- name    : Hairer.testFunction_decomposition_scaledTest
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T06:01:14.966978+00:00
-- url     : https://prove2.me/theorems/5f35dcbf-5c91-491e-8757-2db9ac4cddbd
-- title:
--   Uniform decomposition of a test function into rescaled test functions $S^\delta_{s,x}\eta$
-- statement:
--   **A uniform anisotropic partition of unity at scale $\delta$.**
--
--   Fix a scaling $s=(s_1,\dots,s_d)$ with $s_i\ge 1$, an order $r\in\mathbb N$, and a test
--   function $\varphi\in C^\infty_0(\mathbb R^d)$. Then there are a compact set
--   $K\subseteq\mathbb R^d$ and a constant $M$, depending only on $\varphi$, $s$ and $r$,
--   with the following property. For every $\delta\in(0,1]$ there exist finitely many points
--   $x_1,\dots,x_n\in K$, reals $c_1,\dots,c_n$ and functions
--   $\eta_1,\dots,\eta_n\in\mathcal B^r_{s,0}$ such that
--
--   $$\varphi \;=\; \sum_{i=1}^{n} c_i\, S^{\delta}_{s,x_i}\eta_i ,
--   \qquad \sum_{i=1}^{n} |c_i| \;\le\; M .$$
--
--   Here $\mathcal B^r_{s,0}$ is Hairer's class of test functions supported in the unit ball
--   of the scaled quasi-norm $\|\cdot\|_s$ whose derivatives up to order $r$ are bounded by
--   $1$, and $(S^\delta_{s,x}\eta)(y)=\delta^{-|s|}\eta\big((y_i-x_i)/\delta^{s_i}\big)_i$.
--
--   The decomposition is obtained from a smooth partition of unity subordinate to the
--   anisotropic boxes $\prod_i [x_i-\delta^{s_i},x_i+\delta^{s_i}]$ centred at the points of
--   the lattice $\prod_i \delta^{s_i}\mathbb Z$ that meet the support of $\varphi$. There are
--   $O(\delta^{-|s|})$ such boxes, while each piece $\varphi\psi_i$, rescaled to the unit
--   box, has $C^r$ norm $O(1)$ because every derivative taken in the rescaled variable
--   carries a factor $\delta^{s_j}\le 1$; hence each coefficient is $O(\delta^{|s|})$ and the
--   total mass $\sum_i |c_i|$ stays bounded as $\delta\to 0$.
--
--   The statement is the exact quantitative input needed for the uniqueness clause of
--   Hairer's Theorem 3.10: a distribution that is $O(\delta^{\gamma})$ with $\gamma>0$ on all
--   rescaled test functions $S^\delta_{s,x}\eta$, uniformly over compact sets, annihilates
--   every test function. Because a distribution here is a plain linear functional on
--   $C^\infty_0$, with no continuity assumed, the decomposition must be an exact finite
--   linear combination rather than an approximation.
-- source:
--   Auxiliary lemma for M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014) 269-504, arXiv:1303.5113 (v4), proof of Theorem 3.10 (uniqueness clause), pp. 32-33; it replaces the mollification argument used there, which presupposes continuity of the distribution, by an exact finite partition-of-unity decomposition valid for arbitrary linear functionals on test functions.

import Definitions.Def_Hairer_TestFunctions

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace Hairer

/-- **Anisotropic partition of unity at scale `δ`.**

Every smooth compactly supported test function `φ` on `ℝ^d` can be written, at every
scale `δ ∈ (0,1]`, as a *finite* linear combination
`φ = ∑ᵢ cᵢ · S^δ_{s,xᵢ} ηᵢ`
of rescaled test functions `ηᵢ ∈ B^r_{s,0}` centred at points `xᵢ` of one fixed compact
set, with `∑ᵢ |cᵢ| ≤ M` for a constant `M` depending only on `φ`, `s` and `r`, but not
on `δ`.

The number of terms grows like `δ^{-|s|}` while each coefficient is of size `δ^{|s|}`,
which is exactly what makes the total mass `∑ᵢ|cᵢ|` bounded uniformly in `δ`. -/
theorem testFunction_decomposition_scaledTest
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) (r : ℕ)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) :
    ∃ (K : Set (Pt d)) (M : ℝ), IsCompact K ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ (n : ℕ) (x : Fin n → Pt d) (c : Fin n → ℝ) (η : Fin n → (Pt d → ℝ)),
          (∀ i, x i ∈ K) ∧ (∀ i, IsTestBall s r (η i)) ∧
          (∑ i, |c i|) ≤ M ∧
          ∀ y : Pt d, φ y = ∑ i, c i * scaledTest s δ (x i) (η i) y := by
  sorry

end Hairer
