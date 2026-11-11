-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_B_1
-- name    : GrothendieckPD.Digits.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:24.902892+00:00
-- url     : https://prove2.me/theorems/99915f67-1254-465d-a928-f6558dbaafd5
-- title:
--   Lemma B.1: $v_\infty(q)\le 1000/1773$ for the (B.1) value
-- statement:
--   Let $q$ be the sequence of Eq. (4.1), $Q=Q^{(n)}=\sum_mq_m\Pi_m$ on $L^2(\gamma_n)$, and
--   $$v_n(q)=\mathrm{OPT}(Q)=\sup_{f,g}|\langle f,Qg\rangle|\qquad(B.1)$$
--   over measurable $f,g:\mathbb R^n\to[-1,1]$. Then
--   $$v_\infty(q)=\sup_nv_n(q)\le\frac{1000}{1773}.\qquad(B.2)$$
--
--   This is the numerical core of the lower bound $K_G\ge1.773$.
--
--   Differences from the source:
--   - encoding: c_m(f, g) = ⟨Π_m f, Π_m g⟩ → the moment sum ∑_{|α| = m} E[f He_α] E[g He_α] / α! (GrothendieckLB.pmInner); reason: same value by orthonormality of ψ_α = He_α/√α!
--   - encoding: decimal constants → exact rationals; reason: the source says every decimal is exact
--   - encoding: v_∞(q) = sup over n ∈ ℕ → supremum over n ∈ {0, 1, 2, …}; reason: for n = 0 every function is constant and both game values equal |q_0|, which is 0 for the q in question; this does not change the supremum over positive dimensions
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma B.1, Eq. (B.1)–(B.2), p. 19

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

namespace GrothendieckPD.Digits

/-- Lemma B.1 (p. 19), Eq. (B.2): `v_∞(q) ≤ 1000/1773`, where `v_n(q) = sup_{f,g} |⟨f, Qg⟩|` over
measurable `f, g : ℝ^n → [-1, 1]` (Eq. B.1) and `q` is Eq. (4.1). -/
theorem lemma_B_1 : gameValueB1Inf qCert ≤ 1000 / 1773 := by sorry

end GrothendieckPD.Digits
