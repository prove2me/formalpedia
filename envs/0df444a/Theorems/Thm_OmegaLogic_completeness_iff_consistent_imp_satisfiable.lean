-- Prove2me | Theorems.Thm_OmegaLogic_completeness_iff_consistent_imp_satisfiable
-- name    : OmegaLogic.completeness_iff_consistent_imp_satisfiable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T16:37:06.870373+00:00
-- url     : https://prove2.me/theorems/e69fb4f4-d8cf-4fc0-afdb-71be759c96bd
-- title:
--   Completeness for $T$ $\iff$ (Ω-consistent $\Rightarrow$ Ω-satisfiable)
-- statement:
--   **Fact 3.9 (primer).** For every set of sentences $T$, the following are equivalent:
--
--   1. for every sentence $\varphi$, $T \models_\Omega \varphi$ implies $T \vdash_\Omega \varphi$;
--   2. if $T$ is Ω-consistent ($T \nvdash_\Omega \bot$), then $T$ is Ω-satisfiable (some $V^B_\alpha \models T$).
--
--   $$\Big(\forall \varphi,\ T \models_\Omega \varphi \Rightarrow T \vdash_\Omega \varphi\Big) \iff \Big(T \text{ Ω-consistent} \Rightarrow T \text{ Ω-satisfiable}\Big).$$
--
--   No large-cardinal hypothesis is assumed. The primer gives this as a restatement of the Ω-conjecture: completeness for a fixed theory is equivalent to the model-existence form.
-- source:
--   J. Bagaria, N. Castells, P. Larson, "An Ω-logic primer", in Set Theory (Trends in Mathematics), Birkhäuser 2006, pp. 1–28, doi:10.1007/3-7643-7692-9_1; online version https://paulblarson.github.io/omegalogicmaster5.pdf, Fact 3.9, pp. 24–25.

import Definitions.Def_OmegaLogic_Provability
import Definitions.Def_OmegaLogic_LargeCardinals

universe u

namespace OmegaLogic

theorem completeness_iff_consistent_imp_satisfiable (T : Set Sent) :
    (∀ φ : Sent, OmegaValid.{u} T φ → OmegaProvable.{u} T φ) ↔
      (OmegaConsistent.{u} T → OmegaSatisfiable.{u} T) := by sorry

end OmegaLogic
