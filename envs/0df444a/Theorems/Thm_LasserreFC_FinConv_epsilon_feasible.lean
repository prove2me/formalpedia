-- Prove2me | Theorems.Thm_LasserreFC_FinConv_epsilon_feasible
-- name    : LasserreFC.FinConv.epsilon_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:36.115985+00:00
-- url     : https://prove2.me/theorems/3397a905-93a5-4a01-99c6-293ded1fb3d1
-- title:
--   Proof of Theorem 1.1, p. 8 — f − f_min ∈ I(V_ℝ(h)) + Q(g) ⇒ γ = f_min − ε is feasible in (1.2) at one order k₀ for every ε > 0
-- statement:
--   Let $f_{\min} \in \mathbb R$ and suppose $f - f_{\min} \equiv \sigma_1 \bmod I(V_{\mathbb R}(h))$ for some $\sigma_1 \in Q(g)$, i.e. $f - f_{\min} = q + \sigma_1$ with $q$ vanishing on $V_{\mathbb R}(h)$. Then there is a relaxation order $k_0 \in \mathbb N$ such that
--
--   $$f - (f_{\min} - \varepsilon) \in \langle h\rangle_{2k_0} + Q_{k_0}(g) \qquad \text{for every } \varepsilon > 0,$$
--
--   i.e. $\gamma = f_{\min} - \varepsilon$ is feasible in (1.2) at order $k_0$ for every $\varepsilon > 0$.
--
--   This is the algebraic core of the proof of Theorem 1.1: it converts the representation modulo $I(V_{\mathbb R}(h))$ of Theorem 2.4 into feasibility in the hierarchy at one order that does not depend on $\varepsilon$, so that $f_{k_0} \ge f_{\min}$.
--
--   **Formalization Note** No archimedean hypothesis and no optimality condition is assumed; the step is pure algebra.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 8, proof of Theorem 1.1 (σ_ε, φ_ε and the order k₀)

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy

namespace LasserreFC.FinConv

open MvPolynomial

/-- Proof of Theorem 1.1, p. 8: if `f − f_min ≡ σ₁ mod I(V_ℝ(h))` with `σ₁ ∈ Q(g)`, there is one
relaxation order `k₀` at which `γ = f_min − ε` is feasible in (1.2) for every `ε > 0`. -/
theorem epsilon_feasible {n m1 m2 : ℕ} (P : POP n m1 m2) (fmin : ℝ)
    (hrep : ∃ q ∈ vanishingIdeal ℝ (realVariety P), ∃ σ1 ∈ qmod P, P.f - C fmin = q + σ1) :
    ∃ k0 : ℕ, ∀ ε : ℝ, 0 < ε → P.f - C (fmin - ε) ∈ trunc P k0 := by sorry

end LasserreFC.FinConv
