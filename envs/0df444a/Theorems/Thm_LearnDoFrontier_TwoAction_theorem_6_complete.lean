-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_theorem_6_complete
-- name    : LearnDoFrontier.TwoAction.theorem_6_complete
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:51.492979+00:00
-- url     : https://prove2.me/theorems/dd7f72c2-af48-4b16-8cf8-1f5e6b64891a
-- title:
--   Theorem 6 (Complete), EC p. 11 — the θ-component of (28)–(31) has a unique solution, the root expansion with (α^A; −α^B) = (û^B_θ − û^A_θ)Y⁻¹1, and det Y is explicit
-- statement:
--   Assume the standing assumptions of §5: $0 < \delta < 1$, General Position, Informative Actions A and B, and exact signal quality indices $(n(A,\gamma), n(A,\bar\gamma), n(B,\gamma), n(B,\bar\gamma)) = (n^A, -\bar n^A, n^B, -\bar n^B)$ (Definition 3). Fix $\theta \in \{1, 2\}$, write $p^A_\theta = p_\theta(A,\gamma)$, $p^B_\theta = p_\theta(B,\gamma)$, and let
--   $$f^A_\theta(z) = z^{n^A+\bar n^A} - \delta^{-1}(p^A_\theta)^{-1} z^{\bar n^A} + (p^A_\theta)^{-1}(1 - p^A_\theta),\qquad f^B_\theta(z) = z^{n^B+\bar n^B} - \delta^{-1}(1 - p^B_\theta)^{-1} z^{n^B} + (1 - p^B_\theta)^{-1} p^B_\theta,$$
--   $Z^a_{unit} = \{z : f^a_\theta(z) = 0,\ |z| < 1\}$ and $m^a_z$ the multiplicity of $z \in Z^a_{unit}$. Then:
--
--   1. **Root counts.** $\sum_{z \in Z^A_{unit}} m^A_z = \bar n^A$ and $\sum_{z \in Z^B_{unit}} m^B_z = n^B$.
--   2. For every enumeration $z^A_1, \dots, z^A_{d^A}$ of $Z^A_{unit}$ and $z^B_1, \dots, z^B_{d^B}$ of $Z^B_{unit}$, with $m^a_i = m^a_{z^a_i}$, let $Y = (Y^A, Y^B)$ be the $(\bar n^A + n^B)$-square matrix with $Y^A_{k,(i,\tau)} = \binom{k}{\tau}(z^A_i)^{k-\tau}$ (columns: $i$, then $\tau = 0, \dots, m^A_i - 1$) and $Y^B_{k,(j,\tau)} = \binom{\bar n^A + n^B - 1 - k}{\tau}(z^B_j)^{\bar n^A + n^B - 1 - k - \tau}$ (columns: $j$, then $\tau = m^B_j - 1, \dots, 0$). Then
--   $$\det Y = \prod_{1\le i<l\le d^A}(z^A_l - z^A_i)^{m^A_i m^A_l}\cdot\prod_{i,l}(1 - z^A_i z^B_l)^{m^A_i m^B_l}\cdot\prod_{1\le i<l\le d^B}(z^B_i - z^B_l)^{m^B_i m^B_l} \ne 0.$$
--   3. **Solution.** The $\theta$-th component of (28)–(31) has exactly one pair of real solutions $(v^A_\theta, v^B_\theta)$, and, with the coefficient vectors defined by $\binom{\boldsymbol\alpha^A}{-\boldsymbol\alpha^B} = (\hat u^B_\theta - \hat u^A_\theta) Y^{-1}\mathbf 1$,
--   $$v^A_\theta(k) = \sum_{z \in Z^A_{unit}} \sum_{\tau=0}^{m^A_z - 1} \alpha^A_{z,\tau}\binom{k}{\tau} z^{k-\tau},\qquad v^B_\theta(k) = \sum_{z \in Z^B_{unit}} \sum_{\tau=0}^{m^B_z - 1} \alpha^B_{z,\tau}\binom{k}{\tau} z^{k-\tau}.$$
--
--   This is the paper's closed form for the extreme points of the efficient frontier when both actions are informative: the frontier is the root expansion of two coupled difference equations, and the coupling matrix $Y$ is always invertible.
--
--   **Formalization Note** The enumerations are arbitrary bijections `Fin d ≃ Z_unit`, universally quantified; the determinant identity depends on the column order, which is the paper's (A before B, lexicographic). The root counts are conclusions; they are what make $Y$ square, and $Y$'s size is written $\sum m^A + \sum m^B$, which equals $\bar n^A + n^B$ by (1). The sequences are real and indexed by $k = 0, 1, \dots$; the formula is an identity in $\mathbb C$. The coefficient $\alpha^B_{z_j,\tau}$ is minus the entry of $(\hat u^B_\theta - \hat u^A_\theta)Y^{-1}\mathbf 1$ at the B-column $(j, \tau)$. The link from the efficient frontier to (28)–(31) (Theorem 4) is not part of the statement.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), EC p. 11 (PDF p. 54), Theorem 6 (Complete); p. 28, Theorem 6; pp. 27–28, Eqs. (28)–(31)

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra
import Definitions.Def_LearnDoFrontier_TwoAction_Model

open Matrix

namespace LearnDoFrontier.TwoAction

theorem theorem_6_complete (M : Model) (hM : M.Standing) (θ : Fin 2) :
    (∑ z ∈ Zunit (M.fA θ), mult (M.fA θ) z = M.nbarA ∧
      ∑ z ∈ Zunit (M.fB θ), mult (M.fB θ) z = M.nB) ∧
    ∀ (dA : ℕ) (eA : Fin dA ≃ Zunit (M.fA θ)) (dB : ℕ) (eB : Fin dB ≃ Zunit (M.fB θ)),
      let zA : Fin dA → ℂ := fun i => (eA i : ℂ)
      let mA : Fin dA → ℕ := fun i => mult (M.fA θ) (eA i)
      let zB : Fin dB → ℂ := fun j => (eB j : ℂ)
      let mB : Fin dB → ℕ := fun j => mult (M.fB θ) (eB j)
      let Y := Ymat zA mA zB mB
      let α := Y⁻¹ *ᵥ (fun _ => ((M.bdryConst θ : ℝ) : ℂ))
      let αA : (Σ i : Fin dA, Fin (mA i)) → ℂ := fun p => α (colEquiv mA mB (Sum.inl p))
      let αB : (Σ j : Fin dB, Fin (mB j)) → ℂ :=
        fun p => -α (colEquiv mA mB (Sum.inr ⟨p.1, Fin.rev p.2⟩))
      Y.det = detFormula zA mA zB mB ∧ Y.det ≠ 0 ∧
      (∃! v : (ℕ → ℝ) × (ℕ → ℝ), M.IsBVP θ v.1 v.2) ∧
      ∀ vA vB : ℕ → ℝ, M.IsBVP θ vA vB → ∀ k : ℕ,
        ((vA k : ℝ) : ℂ) = rootExp zA mA αA k ∧ ((vB k : ℝ) : ℂ) = rootExp zB mB αB k := by sorry

end LearnDoFrontier.TwoAction
