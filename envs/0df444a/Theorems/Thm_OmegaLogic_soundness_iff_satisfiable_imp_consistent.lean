-- Prove2me | Theorems.Thm_OmegaLogic_soundness_iff_satisfiable_imp_consistent
-- name    : OmegaLogic.soundness_iff_satisfiable_imp_consistent
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T16:34:46.196211+00:00
-- url     : https://prove2.me/theorems/735f1541-5a2e-4229-bd3c-3f70ac20ba62
-- title:
--   Soundness for $T$ $\iff$ (Ω-satisfiable $\Rightarrow$ Ω-consistent)
-- statement:
--   **Fact 3.4 (primer).** For every set of sentences $T$, the following are equivalent:
--
--   1. for every sentence $\varphi$, $T \vdash_\Omega \varphi$ implies $T \models_\Omega \varphi$;
--   2. if $T$ is Ω-satisfiable (some $V^B_\alpha \models T$), then $T$ is Ω-consistent ($T \nvdash_\Omega \bot$).
--
--   $$\Big(\forall \varphi,\ T \vdash_\Omega \varphi \Rightarrow T \models_\Omega \varphi\Big) \iff \Big(T \text{ Ω-satisfiable} \Rightarrow T \text{ Ω-consistent}\Big).$$
--
--   No large-cardinal hypothesis is assumed. This restates soundness for a fixed theory as a statement about consistency.
-- source:
--   J. Bagaria, N. Castells, P. Larson, "An Ω-logic primer", in Set Theory (Trends in Mathematics), Birkhäuser 2006, pp. 1–28, doi:10.1007/3-7643-7692-9_1; online version https://paulblarson.github.io/omegalogicmaster5.pdf, Fact 3.4, p. 23.

import Definitions.Def_OmegaLogic_Provability
import Definitions.Def_OmegaLogic_LargeCardinals

universe u

namespace OmegaLogic

theorem soundness_iff_satisfiable_imp_consistent (T : Set Sent) :
    (∀ φ : Sent, OmegaProvable.{u} T φ → OmegaValid.{u} T φ) ↔
      (OmegaSatisfiable.{u} T → OmegaConsistent.{u} T) := by sorry

end OmegaLogic
