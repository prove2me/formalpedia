-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_product_identity
-- name    : GOSNIZK.DLINCommit.product_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:31.224642+00:00
-- url     : https://prove2.me/theorems/d4adcdab-8fbe-40ba-93c2-97f54305bffa
-- title:
--   Proof of Theorem 4 (p. 13) — (r₀ + s₀ − t₀)(r₁ + s₁ − t₁) = 0, so t₀ = r₀ + s₀ or t₁ = r₁ + s₁
-- statement:
--   Let $p$ be a prime and let $r_0, s_0, t_0, r_1, s_1, t_1$ and $m_{ij}$ ($i = 1, 2$, $j = 1, 2, 3$) be elements of $\mathbb Z_p$. Put $m_{3j} = m_{1j} + m_{2j}$ and assume the six equations
--   $$\begin{aligned} m_{11} &= r_0 r_1, & m_{12} + m_{21} &= r_0 s_1 + s_0 r_1,\\ m_{22} &= s_0 s_1, & m_{13} + m_{31} &= r_0 t_1 + t_0 r_1,\\ m_{33} &= t_0 t_1, & m_{23} + m_{32} &= s_0 t_1 + t_0 s_1. \end{aligned}$$
--   Then
--   $$\begin{aligned} (r_0 + s_0 - t_0)(r_1 + s_1 - t_1) &= r_0r_1 + r_0s_1 + s_0r_1 + s_0s_1 + t_0t_1 - (r_0t_1 + t_0r_1 + s_0t_1 + t_0s_1)\\ &= m_{11} + m_{12} + m_{21} + m_{22} + m_{33} - m_{13} - m_{31} - m_{23} - m_{32} = 0, \end{aligned}$$
--   and therefore $t_0 = r_0 + s_0$ or $t_1 = r_1 + s_1$.
--
--   This is the algebraic core of the soundness proof: one of the two candidate openings of the commitment is a linear tuple.
--
--   **Formalization Note** The auxiliary $m_{3j}$ are written out as $m_{1j} + m_{2j}$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, proof of Theorem 4 ('This means ... We conclude')

import Mathlib

namespace GOSNIZK.DLINCommit

/-- Proof of Theorem 4, p. 13: from the six exponent equations (with `m₃₁ = m₁₁ + m₂₁`,
`m₃₂ = m₁₂ + m₂₂`, `m₃₃ = m₁₃ + m₂₃`) over `ℤ_p`, `p` prime,
`(r₀ + s₀ − t₀)(r₁ + s₁ − t₁) = m₁₁ + m₁₂ + m₂₁ + m₂₂ + m₃₃ − m₁₃ − m₃₁ − m₂₃ − m₃₂ = 0`, hence
`t₀ = r₀ + s₀` or `t₁ = r₁ + s₁`. -/
theorem product_identity (p : ℕ) [Fact p.Prime]
    (r₀ s₀ t₀ r₁ s₁ t₁ m₁₁ m₁₂ m₁₃ m₂₁ m₂₂ m₂₃ : ZMod p)
    (e₁ : m₁₁ = r₀ * r₁) (e₂ : m₂₂ = s₀ * s₁) (e₃ : m₁₃ + m₂₃ = t₀ * t₁)
    (e₄ : m₁₂ + m₂₁ = r₀ * s₁ + s₀ * r₁)
    (e₅ : m₁₃ + (m₁₁ + m₂₁) = r₀ * t₁ + t₀ * r₁)
    (e₆ : m₂₃ + (m₁₂ + m₂₂) = s₀ * t₁ + t₀ * s₁) :
    (r₀ + s₀ - t₀) * (r₁ + s₁ - t₁) =
        r₀ * r₁ + r₀ * s₁ + s₀ * r₁ + s₀ * s₁ + t₀ * t₁ - (r₀ * t₁ + t₀ * r₁ + s₀ * t₁ + t₀ * s₁) ∧
      r₀ * r₁ + r₀ * s₁ + s₀ * r₁ + s₀ * s₁ + t₀ * t₁ - (r₀ * t₁ + t₀ * r₁ + s₀ * t₁ + t₀ * s₁) =
        m₁₁ + m₁₂ + m₂₁ + m₂₂ + (m₁₃ + m₂₃) - m₁₃ - (m₁₁ + m₂₁) - m₂₃ - (m₁₂ + m₂₂) ∧
      m₁₁ + m₁₂ + m₂₁ + m₂₂ + (m₁₃ + m₂₃) - m₁₃ - (m₁₁ + m₂₁) - m₂₃ - (m₁₂ + m₂₂) = 0 ∧
      (t₀ = r₀ + s₀ ∨ t₁ = r₁ + s₁) := by sorry

end GOSNIZK.DLINCommit
