-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_theorem_3
-- name    : LearnDoFrontier.TwoAction.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:42.626631+00:00
-- url     : https://prove2.me/theorems/d706a665-79b7-4cf2-a588-528b959c37ed
-- title:
--   Theorem 3, p. 22 — the θ-component of (13)–(15) is solved by the root expansion over the roots of f_θ in the unit disk, α = (û^B_θ − û^A_θ)Y⁻¹1
-- statement:
--   Assume the setting of §4: $0 < \delta < 1$, General Position, Informative Action A, Uninformative Action B, and the signal quality indices $n(A,\gamma) = n^A > 0$, $n(A,\bar\gamma) = -\bar n^A < 0$ of Definition 2. Fix $\theta \in \{1, 2\}$ and let
--   $$f_\theta(z) = z^{n^A + \bar n^A} - \delta^{-1} p_\theta(A,\gamma)^{-1} z^{\bar n^A} + p_\theta(A,\gamma)^{-1} p_\theta(A,\bar\gamma),$$
--   $Z_{unit} = \{z : f_\theta(z) = 0,\ |z| < 1\}$ and $m_z$ the multiplicity of $z$. Then:
--
--   1. $\sum_{z \in Z_{unit}} m_z = \bar n^A$.
--   2. For every labelling $j \mapsto (z(j), \tau(j))$, $j = 1, \dots, \bar n^A$, of the pairs $(z, \tau)$ with $z \in Z_{unit}$ and $0 \le \tau \le m_z - 1$, the square matrix $Y = (y_{kj})$, $y_{kj} = k^{\tau(j)} z(j)^k$ for $k = 0, \dots, \bar n^A - 1$, is nonsingular.
--   3. The $\theta$-th component of (13)–(15) has exactly one real solution $v^A_\theta : \mathbb N \to \mathbb R$, and with $\alpha = (\hat u^B_\theta - \hat u^A_\theta) Y^{-1}\mathbf 1$ it is
--   $$v^A_\theta(k) = \sum_{j=1}^{\bar n^A} \alpha_j\, k^{\tau(j)} z(j)^k = \sum_{z \in Z_{unit}} \Big(\sum_{\tau=0}^{m_z - 1} \alpha_{z,\tau} k^\tau\Big) z^k.$$
--
--   This is the paper's closed form for the efficient frontier when the second action is a stopping action, the one-sided version of Theorem 6.
--
--   **Formalization Note** The labelling is an arbitrary bijection from $\{0, \dots, \bar n^A - 1\}$ onto the pairs, universally quantified, matching "order $\{\alpha_{z,\tau}\}$ arbitrarily". The root count (1) is a conclusion, not a hypothesis; without it no such bijection exists. The solution is real and the formula is an identity in $\mathbb C$. The hypotheses are the §4 standing assumptions as printed, although the conclusion only uses $\delta, p_\theta(A,\gamma) \in (0,1)$ and $n^A, \bar n^A > 0$.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), p. 22, Theorem 3; p. 20, Eqs. (13)–(15); proof EC pp. 3–4

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra
import Definitions.Def_LearnDoFrontier_TwoAction_Model

open Matrix

namespace LearnDoFrontier.TwoAction

theorem theorem_3 (M : Model) (hM : M.Standing4) (θ : Fin 2) :
    ∑ z ∈ Zunit (M.fA θ), mult (M.fA θ) z = M.nbarA ∧
    ∀ σ : Fin M.nbarA ≃ (Σ z : Zunit (M.fA θ), Fin (mult (M.fA θ) z)),
      let Y : Matrix (Fin M.nbarA) (Fin M.nbarA) ℂ :=
        Y3mat (fun j => (((σ j).1 : ℂ), ((σ j).2 : ℕ)))
      let α : Fin M.nbarA → ℂ := Y⁻¹ *ᵥ (fun _ => ((M.bdryConst θ : ℝ) : ℂ))
      Y.det ≠ 0 ∧ (∃! v : ℕ → ℝ, M.IsBVP3 θ v) ∧
      ∀ v : ℕ → ℝ, M.IsBVP3 θ v → ∀ k : ℕ,
        ((v k : ℝ) : ℂ) = ∑ j : Fin M.nbarA, α j * (k : ℂ) ^ ((σ j).2 : ℕ) * ((σ j).1 : ℂ) ^ k := by sorry

end LearnDoFrontier.TwoAction
