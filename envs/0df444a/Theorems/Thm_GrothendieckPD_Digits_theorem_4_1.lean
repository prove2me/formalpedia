-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_theorem_4_1
-- name    : GrothendieckPD.Digits.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:11.383084+00:00
-- url     : https://prove2.me/theorems/8e95cf95-1068-4c14-adbe-1ccbca421110
-- title:
--   Theorem 4.1: $v_\infty(q)\le1000/1773$, therefore $K_G\ge1.773$
-- statement:
--   Let $q$ be the explicit odd sequence of Eq. (4.1) ($q_1=1$, $q_3=-0.654509751718$, …, $q_{21}=0.016668224599$, all other $q_m=0$; every decimal exact) and $v_\infty(q)=\sup_n\sup_{f,g:\mathbb R^n\to\{\pm1\}}\sum_mq_m\langle\Pi_mf,\Pi_mg\rangle$. Then
--   $$v_\infty(q)\le\frac{1000}{1773}.$$
--   Therefore $K_G\ge1.773$.
--
--   This is the lower half of the main theorem: an explicit Hermite projection game with integrality gap at least $1.773$.
--
--   Differences from the source:
--   - encoding: f, g : ℝⁿ → {±1} → measurable functions with values in {1, −1} (GrothendieckLB.IsSignFn); reason: Hermite coefficients require measurability; the source states it in Lemma 2.5 and uses it throughout
--   - encoding: c_m(f, g) = ⟨Π_m f, Π_m g⟩ → the moment sum ∑_{|α| = m} E[f He_α] E[g He_α] / α! (GrothendieckLB.pmInner); reason: same value by orthonormality of ψ_α = He_α/√α!
--   - encoding: decimal constants → exact rationals; reason: the source says every decimal is exact
--   - encoding: v_∞(q) = sup over n ∈ ℕ → supremum over n ∈ {0, 1, 2, …}; reason: for n = 0 every function is constant and both game values equal |q_0|, which is 0 for the q in question; this does not change the supremum over positive dimensions
--   - encoding: K_G = sup_{m,n} sup_{A} SDP(A)/OPT(A) (Eq. 1.1) → K_G = inf{K : SDP(A) ≤ K·OPT(A) for all real matrices A} (published GrothendieckConstant.grothendieckConst), with unit vectors in ℝ^d for arbitrary d; reason: same value: the ratio is undefined only at A = 0, where both sides vanish; OPT(A) > 0 for A ≠ 0; the admissible set is nonempty (Grothendieck's inequality) and bounded below; unit vectors in any dimension give the same SDP value as in ℝ^{m+n}
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Theorem 4.1 and Eq. (4.1), p. 11

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

namespace GrothendieckPD.Digits

/-- Theorem 4.1 (p. 11): for `q` of Eq. (4.1), `v_∞(q) ≤ 1000/1773`; therefore `K_G ≥ 1.773`. -/
theorem theorem_4_1 :
    gameValueInf qCert ≤ 1000 / 1773 ∧
      (1773 / 1000 : ℝ) ≤ GrothendieckConstant.grothendieckConst := by sorry

end GrothendieckPD.Digits
