-- Prove2me | Theorems.Thm_JointMixND_QuadOT_Supplement_lemma_1
-- name    : JointMixND.QuadOT.Supplement.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:13:10.818416+00:00
-- url     : https://prove2.me/theorems/b9ebc413-093f-4b68-bd72-0831bfa912f2
-- title:
--   Lemma 1, p. 17 — an elliptical vector E_n(μ, Σ, ψ) is a joint mix iff 1ᵀΣ1 = 0 or ψ = 1 on ℝ₊
-- statement:
--   Let $\mathbf X\sim\mathrm E_n(\boldsymbol\mu,\Sigma,\psi)$ be an $n$-dimensional elliptical random vector: its characteristic function is $\mathbf t\mapsto\exp(\mathrm i\,\mathbf t^\top\boldsymbol\mu)\,\psi(\mathbf t^\top\Sigma\mathbf t)$, with $\Sigma$ symmetric positive semidefinite. Then $\mathbf X$ is a joint mix if and only if
--
--   $$\mathbf 1_n^\top\Sigma\mathbf 1_n=0\quad\text{or}\quad\psi(s)=1\ \text{for all }s\ge0.$$
--
--   No non-degeneracy is assumed. The lemma identifies the elliptical joint mixes and is used in the proof of Theorem 6 to show that $\mathrm E_n(\mathbf 0_n,P^*_n,\psi)$ is a joint mix.
--
--   **Formalization Note** The law is given through its characteristic function (16). $\psi$ is a function $\mathbb R\to\mathbb R$ whose values on $[0,\infty)$ are the only ones that enter.
--
--   Differences from the source:
--   - encoding: X ∼ E_n(μ, Σ, ψ), ψ = 1 on ℝ₊ → the law P satisfies (16) with S := Σ; ∀ s ≥ 0, ψ s = 1; reason: Σ is a reserved symbol in Lean; same instances
--   - generalization: vectors of positive dimension n → n : ℕ, including n = 0; reason: at n = 0 the empty sum is constant and the quadratic form is zero; all positive-dimensional source instances are retained
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 17, Lemma 1 (proof pp. 29–30)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Elliptical

open MeasureTheory ProbabilityTheory Matrix

namespace JointMixND.QuadOT.Supplement

theorem lemma_1 {n : ℕ} (ψ : ℝ → ℝ) (μ : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (P : Measure (Fin n → ℝ)) (hP : IsElliptical ψ μ S P) :
    IsJointMix P ↔
      ((1 : Fin n → ℝ) ⬝ᵥ (S *ᵥ (1 : Fin n → ℝ)) = 0 ∨ ∀ s : ℝ, 0 ≤ s → ψ s = 1) := by sorry

end JointMixND.QuadOT.Supplement
