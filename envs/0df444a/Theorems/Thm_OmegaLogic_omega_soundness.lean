-- Prove2me | Theorems.Thm_OmegaLogic_omega_soundness
-- name    : OmegaLogic.omega_soundness
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T16:34:09.408268+00:00
-- url     : https://prove2.me/theorems/1c8e0aed-e608-4768-9b13-2b015f3e006f
-- title:
--   Soundness of Ω-logic: $T \vdash_\Omega \varphi \Rightarrow T \models_\Omega \varphi$
-- statement:
--   **Soundness of Ω-logic** (Woodin; primer, Theorem 3.3). Assume there is a proper class of strongly inaccessible cardinals. Then for every set of sentences $T$ and every sentence $\varphi$,
--   $$T \vdash_\Omega \varphi \ \Longrightarrow\ T \models_\Omega \varphi .$$
--
--   That is, if a universally Baire set $A$ has the property that $M_\alpha \models T$ implies $M_\alpha \models \varphi$ for every strongly $A$-closed countable transitive model $M$ of ZFC and every ordinal $\alpha \in M$, then $V^B_\alpha \models T$ implies $V^B_\alpha \models \varphi$ for every complete Boolean algebra $B$ and every ordinal $\alpha$.
--
--   This is the "if" direction of the Ω-conjecture.
-- source:
--   Wikipedia, "Ω-logic" (revision oldid=1336097018), section "Analysis", last paragraph ("Woodin showed that this notion of 'provability' implies Ω-validity"); precise statement from J. Bagaria, N. Castells, P. Larson, "An Ω-logic primer", in Set Theory (Trends in Mathematics), Birkhäuser 2006, pp. 1–28, doi:10.1007/3-7643-7692-9_1; online version https://paulblarson.github.io/omegalogicmaster5.pdf, Theorem 3.3 (Soundness), p. 23.

import Definitions.Def_OmegaLogic_Provability
import Definitions.Def_OmegaLogic_LargeCardinals

universe u

namespace OmegaLogic

theorem omega_soundness (hI : ProperClassInaccessible.{u}) (T : Set Sent) (φ : Sent) :
    OmegaProvable.{u} T φ → OmegaValid.{u} T φ := by sorry

end OmegaLogic
