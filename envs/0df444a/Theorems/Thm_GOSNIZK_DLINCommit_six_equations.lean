-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_six_equations
-- name    : GOSNIZK.DLINCommit.six_equations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:09.918081+00:00
-- url     : https://prove2.me/theorems/5b183ce6-8517-4850-a8bc-ed39e7707a58
-- title:
--   Proof of Theorem 4 (p. 13) — an accepted proof gives the six exponent equations
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and $ck = (f, h, u, v, w)$ a perfectly binding commitment key of Figure 2. Let $c \in \mathbb G^3$ and $\pi \in \mathbb G^6$, and write them through exponents in $\mathbb Z_p$:
--   $$c = (f^{r_0}, h^{s_0}, g^{t_0}) = (u f^{r_1}, v h^{s_1}, w g^{t_1}),$$
--   $$\pi_{i1} = f^{m_{i1}}, \quad \pi_{i2} = h^{m_{i2}}, \quad \pi_{i3} = g^{m_{i3}} \qquad (i = 1, 2),$$
--   and put $m_{3j} = m_{1j} + m_{2j}$ for $j = 1, 2, 3$. If $V_{01}(ck, c, \pi)$ accepts, then
--   $$\begin{aligned} m_{11} &= r_0 r_1, & m_{12} + m_{21} &= r_0 s_1 + s_0 r_1,\\ m_{22} &= s_0 s_1, & m_{13} + m_{31} &= r_0 t_1 + t_0 r_1,\\ m_{33} &= t_0 t_1, & m_{23} + m_{32} &= s_0 t_1 + t_0 s_1. \end{aligned}$$
--
--   The six pairing equations of the verifier thus become six equations between discrete logarithms; this is the first step of the soundness proof.
--
--   **Formalization Note** The exponents are the discrete logarithms of the paper ($m_{i1} = \log_f \pi_{i1}$, $m_{i2} = \log_h \pi_{i2}$, $m_{i3} = \log_g \pi_{i3}$); they are taken as variables together with hypotheses expressing $c$ and $\pi$ as powers, which can always be met because $f$, $h$, $g$ generate $\mathbb G$. The paper writes "$m_{i2} = \log_h(\pi_{i1})$", a typo for $\log_h(\pi_{i2})$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, proof of Theorem 4 ('From the verification we get')

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Proof of Theorem 4, p. 13: on a perfectly binding key, write `c = (f^{r₀}, h^{s₀}, g^{t₀})`,
`c = (u f^{r₁}, v h^{s₁}, w g^{t₁})` and `π₁ⱼ, π₂ⱼ` as powers `f^{m_{i1}}`, `h^{m_{i2}}`, `g^{m_{i3}}`
(`i = 1, 2`); put `m_{3j} = m_{1j} + m_{2j}`. If `V01(ck, c, π)` accepts, then
`m₁₁ = r₀r₁`, `m₂₂ = s₀s₁`, `m₃₃ = t₀t₁`, `m₁₂ + m₂₁ = r₀s₁ + s₀r₁`, `m₁₃ + m₃₁ = r₀t₁ + t₀r₁`,
`m₂₃ + m₃₂ = s₀t₁ + t₀s₁` in `ℤ_p`. -/
theorem six_equations (S : DLINSetup G GT) (ck : CommitKey G) (xk : ZMod S.p × ZMod S.p × ZMod S.p)
    (hck : S.IsBindingKey ck xk) (c : G × G × G) (π : Proof01 G)
    (r₀ s₀ t₀ r₁ s₁ t₁ : ZMod S.p)
    (h₀ : c = (ck.f ^ r₀.val, ck.h ^ s₀.val, S.g ^ t₀.val))
    (h₁ : c = (ck.u * ck.f ^ r₁.val, ck.v * ck.h ^ s₁.val, ck.w * S.g ^ t₁.val))
    (m₁₁ m₁₂ m₁₃ m₂₁ m₂₂ m₂₃ : ZMod S.p)
    (hπ : π = ⟨ck.f ^ m₁₁.val, ck.h ^ m₁₂.val, S.g ^ m₁₃.val,
               ck.f ^ m₂₁.val, ck.h ^ m₂₂.val, S.g ^ m₂₃.val⟩)
    (hV : S.V01 ck c π) :
    m₁₁ = r₀ * r₁ ∧ m₂₂ = s₀ * s₁ ∧ m₁₃ + m₂₃ = t₀ * t₁ ∧
      m₁₂ + m₂₁ = r₀ * s₁ + s₀ * r₁ ∧
      m₁₃ + (m₁₁ + m₂₁) = r₀ * t₁ + t₀ * r₁ ∧
      m₂₃ + (m₁₂ + m₂₂) = s₀ * t₁ + t₀ * s₁ := by sorry

end GOSNIZK.DLINCommit
