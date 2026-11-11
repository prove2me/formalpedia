-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_B_1
-- name    : HZFixp.Main.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:36.61519+00:00
-- url     : https://prove2.me/theorems/dd3e18b7-6efb-4ea8-b718-b3ea197a0334
-- title:
--   Lemma B.1 — harmonic gate: Q > 0, f(1, A, B) = H_ρ(A, B), 0 < m₀ ≤ f_y ≤ M_f
-- statement:
--   Let $\rho\in(0,1)$ and $0<a_1<b_1<a_2<b_2$. Throughout the harmonic gate's declared intervals ($A\in[a_1,b_1]$, $B\in[a_2,b_2]$, $y\in[0.999,1.001]$), with $Q(y,A,B)=\rho/(y+A)+(1-\rho)/(y+B)$ and $f = 1/Q - y$:
--   $$Q>0,\qquad f(1,A,B)=H_\rho(A,B),\qquad 0<m_0\le \frac{\partial f}{\partial y}(y,A,B)\le M_f,$$
--   with $m_0=\dfrac{\rho(1-\rho)(a_2-b_1)^2}{(1.001+\rho b_2+(1-\rho)b_1)^2}$ and $M_f=\dfrac{\rho(1-\rho)(b_2-a_1)^2}{(0.999+\rho a_2+(1-\rho)a_1)^2}$. Moreover $H_\rho(A,B)$ lies in the declared output interval: in every $[\ell,u]$ with $0<\ell\le H_\rho(a_1,a_2)$ and $H_\rho(b_1,b_2)\le u$.
--
--   These are the derivative and positivity conditions under which Lemma 3.7 applies to harmonic gates.
--
--   Differences from the source:
--   - generalization: rational ρ and endpoints → real ρ and endpoints; reason: pointwise real analysis; rational values are a special case
--   - reading: harmonic gate on inputs A ∈ [a_1, b_1], B ∈ [a_2, b_2] (§3.3.2, Figure 5) → 0 < a_1 < b_1 < a_2 < b_2 and 0 < ρ < 1; reason: the separated input intervals b_1 < a_2 are what B.1.2 verifies ("the separated intervals"; every harmonic gate of §3.3.1 has them), node intervals lie in (0, ∞) (p. 6), and ρ, 1 − ρ are edge multiplicities, hence positive
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 50 (PDF 52), Lemma B.1 and the definitions of m_0, M_f above it

import Mathlib
import Definitions.Def_HZFixp_Main_Gates

namespace HZFixp.Main

/-- **Lemma B.1.** Throughout the harmonic gate's declared intervals, `Q > 0`,
`f(1, A, B) = H_ρ(A, B)`, and `0 < m_0 ≤ f_y ≤ M_f`. The intended output `H_ρ(A, B)` lies in the
declared output interval. -/
theorem lemma_B_1 (ρ a₁ b₁ a₂ b₂ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (ha₁ : 0 < a₁) (h₁ : a₁ < b₁)
    (h₂ : b₁ < a₂) (h₃ : a₂ < b₂) :
    0 < harmM0 ρ a₁ b₁ a₂ b₂ ∧
    ∀ A ∈ Set.Icc a₁ b₁, ∀ B ∈ Set.Icc a₂ b₂,
      harmF ρ 1 A B = harmH ρ A B ∧
      (∀ ℓ u : ℝ, 0 < ℓ → ℓ ≤ harmH ρ a₁ a₂ → harmH ρ b₁ b₂ ≤ u → harmH ρ A B ∈ Set.Icc ℓ u) ∧
      ∀ y ∈ Set.Icc (0.999 : ℝ) 1.001,
        0 < harmQ ρ y A B ∧
        harmM0 ρ a₁ b₁ a₂ b₂ ≤ deriv (fun t => harmF ρ t A B) y ∧
        deriv (fun t => harmF ρ t A B) y ≤ harmMf ρ a₁ b₁ a₂ b₂ := by sorry

end HZFixp.Main
