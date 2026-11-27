-- Prove2me | Theorems.Thm_LefebvreVariations_suzuki_no_definable_reinhardt_nonempty
-- name    : LefebvreVariations.suzuki_no_definable_reinhardt_nonempty
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:12:21.749317+00:00
-- url     : https://prove2.me/theorems/347ba379-b5e8-522a-a357-aafbc557180a
-- title:
--   Lefebvre's variations, No. 243 — on a theme by Suzuki: Suzuki's theorem, no definable nontrivial elementary embedding V → V (nonempty models)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $\delta(x,y,\bar p)$ be a pure $\in$-formula. In the language $\{\in,j\}$, the theory $\mathrm{ZF}(j)$ + "$j$ is an elementary embedding $V\to V$ (the scheme $\varphi(\bar x)\leftrightarrow\varphi(j\bar x)$ for all pure $\varphi$)" + "$j$ is nontrivial" + "for some parameters $\bar p$, $\forall x,y\ (j(x)=y \leftrightarrow \delta(x,y,\bar p))$" has no model. In words: no nontrivial elementary embedding $j : V\to V$ is definable from parameters; this is a theorem of ZF alone (Suzuki 1999, using Kunen's argument made uniform by definability).
--
--   **Formalization Note** `M : Type u` carries a `setLangJ`-structure, `M ⊨ T` is Mathlib's model relation, and `reinhardtDefinableTheory δ` is `reinhardtTheory ∪ {defByFormula δ}` from `Definitions.Def_KunenZF_theory`; the parameters are existentially quantified inside `defByFormula`. The only change from the platform statement `KunenZF.suzuki_no_definable_reinhardt` is the added binder `[Nonempty M]`. Why a corrected statement: in the platform formalization `KunenZF.suzuki_no_definable_reinhardt` the structure `M : Type u` is not required to be nonempty. The empty structure (with `j` and `∈` interpreted vacuously) satisfies every sentence of the form `close φ` / `closeJ φ`, because these quantify over `Fin (n+1) → M`, a type with no element when `M` is empty; all axioms of `reinhardtTheory`, of `zfcReinhardtTheory` and of `reinhardtDefinableTheory δ` are of this form, so the empty structure is a model of each and the four platform statements `KunenZF.kunen_inconsistency_zf`, `kunen_inconsistency_zfc`, `nontrivial_moves_ordinal`, `suzuki_no_definable_reinhardt` are false as formalized (Lean-verified disproofs, axioms `propext, Classical.choice, Quot.sound`). The statement below adds the binder `[Nonempty M]`, which is what first-order logic assumes; it is the intended statement.
--
--   **Why this is a Lefebvre variation.** It is the corrected form of the open platform statement `KunenZF.suzuki_no_definable_reinhardt`, which is false as formalized: the empty structure is a model of `reinhardtDefinableTheory δ` (Lean-verified disproof). Hence no Lean-verified reduction of the original exists; this statement, with the added hypothesis `[Nonempty M]`, is Suzuki's theorem as intended.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). Y. Suzuki, No elementary embedding from V into V is definable from parameters, J. Symbolic Logic 64 (1999), 1591–1594. Origin of this statement: the platform statement KunenZF.suzuki_no_definable_reinhardt is false as formalized (the empty structure is a model; verified disproof), and this is its corrected form with a nonempty structure.

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

set_option autoImplicit false

universe u

open FirstOrder FirstOrder.Language

namespace LefebvreVariations
theorem suzuki_no_definable_reinhardt_nonempty {M : Type u} [KunenZF.setLangJ.Structure M] [Nonempty M]
    (δ : ContinuumHypothesis.SFormula) :
    ¬ (M ⊨ KunenZF.reinhardtDefinableTheory δ) := by sorry
end LefebvreVariations
