-- Prove2me | Theorems.Thm_ModularCurve_LevelP_isLevelPStructure_borelDataPrime
-- name    : ModularCurve.LevelP.isLevelPStructure_borelDataPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b6a06755-bd91-5b48-bb4c-874846541f7c
-- title:
--   The universal Borel pair is a level-p structure
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and let $a$ be a natural number with $1 \le a$ and $a \le (p-1)/2$. Write $\mathcal{B} =$ [`ModularCurve.LevelP.BorelRing p a`](def/ModularCurve_KatzLevelPClassifyingMaps.html#L480) for the localisation of `BorelPRing p a` $=$ `TorsionPointRing (borelQCurve p a) p` away from the element `borelDenom p a`, and let $E =$ `borelCurve p a` be the Weierstrass curve over $\mathcal{B}$ obtained from the universal level-$p$ basis curve `univCurveT p` by base change along the ring map `BorelRing.ofUniv p a`. Let `borelData' p a` be the level-$p$ datum over $\mathcal{B}$ whose four entries $x_P, y_P, x_Q, y_Q$ are the images under the structure map `BorelPRing p a →` $\mathcal{B}$ of `BorelPRing.xP p a`, `BorelPRing.yP p a`, `BorelPRing.xQ p a`, `BorelPRing.yQ p a`. The assertion is that this datum is a level-$p$ structure on $E$ in the sense of `IsLevelPStructure`, that is: $(x_P, y_P)$ and $(x_Q, y_Q)$ both satisfy the affine Weierstrass equation of $E$; the $p$-division polynomial `preΨ p` of $E$ vanishes at $x_P$ and at $x_Q$; and both independence elements $\prod_{b=1}^{(p-1)/2}\bigl(x_Q\,\Psi_b^2(x_P) - \Phi_b(x_P)\bigr)$ and $\prod_{b=1}^{(p-1)/2}\bigl(x_P\,\Psi_b^2(x_Q) - \Phi_b(x_Q)\bigr)$ are units in $\mathcal{B}$.
--
--   This exhibits the Borel ring of exponent $a$ as carrying a second level-$p$ structure on the universal curve, the pair $(P',Q')$ with $x(Q') = x([a]Q)$, so that `borelCurve`/`borelData'` may be fed into the classifying maps for level-$p$ structures. It is used in the construction and evaluation of Katz forms of level $\Gamma_0(p)$, namely by [`ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field`](thm.html#ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field) and [`ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le`](thm.html#ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_isLevelPStructure_borelDataPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.LevelP.isLevelPStructure_borelDataPrime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    ModularCurve.IsLevelPStructure (ModularCurve.LevelP.borelCurve p a) p
      (ModularCurve.LevelP.borelData' p a) := by sorry
