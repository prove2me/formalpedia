-- Prove2me | Theorems.Thm_LefebvreVariations_kunen_inconsistency_zfc_nonempty
-- name    : LefebvreVariations.kunen_inconsistency_zfc_nonempty
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:12:57.480402+00:00
-- url     : https://prove2.me/theorems/abdf67f2-a0b0-50a5-9aaf-7f6356562f73
-- title:
--   Lefebvre's variations, No. 244 — on a theme by Kunen: the Kunen inconsistency in ZFC (nonempty models)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   In the language $\{\in,j\}$, the theory $\mathrm{ZFC}(j)$ (ZFC with Separation and Collection for all $\{\in,j\}$-formulas) + "$j$ is an elementary embedding $V\to V$ for all pure $\in$-formulas" + "$j$ is nontrivial" has no model. That is, there is no nontrivial elementary embedding $j : V \to V$ in ZFC (Kunen's inconsistency theorem).
--
--   Proof sketch (Kunen 1971): $j$ has a critical point $\kappa$ (Lemma 4(2) of Hamkins–Kirmayer–Perlmutter). Let $\lambda=\sup_n j^n(\kappa)$, so $j(\lambda)=\lambda$. By Erdős–Hajnal and Kunen there is an $\omega$-Jónsson function $f:[\lambda]^\omega\to\lambda$; elementarity applied to $f$ and to $j``\lambda$ contradicts the Jónsson property.
--
--   **Formalization Note** `M : Type u` carries a `setLangJ`-structure and `M ⊨ T` is Mathlib's model relation; `zfcReinhardtTheory` is `reinhardtTheory ∪ {incl.onSentence acSentence}` from `Definitions.Def_KunenZF_theory`. The only change from the platform statement `KunenZF.kunen_inconsistency_zfc` is the added binder `[Nonempty M]`. Why a corrected statement: in the platform formalization `KunenZF.kunen_inconsistency_zfc` the structure `M : Type u` is not required to be nonempty. The empty structure (with `j` and `∈` interpreted vacuously) satisfies every sentence of the form `close φ` / `closeJ φ`, because these quantify over `Fin (n+1) → M`, a type with no element when `M` is empty; all axioms of `reinhardtTheory`, of `zfcReinhardtTheory` and of `reinhardtDefinableTheory δ` are of this form, so the empty structure is a model of each and the four platform statements `KunenZF.kunen_inconsistency_zf`, `kunen_inconsistency_zfc`, `nontrivial_moves_ordinal`, `suzuki_no_definable_reinhardt` are false as formalized (Lean-verified disproofs, axioms `propext, Classical.choice, Quot.sound`). The statement below adds the binder `[Nonempty M]`, which is what first-order logic assumes; it is the intended statement.
--
--   **Why this is a Lefebvre variation.** It is the corrected form of the open platform statement `KunenZF.kunen_inconsistency_zfc`, which is false as formalized: the empty structure is a model of `zfcReinhardtTheory` (Lean-verified disproof). Hence no Lean-verified reduction of the original exists; this statement, with the added hypothesis `[Nonempty M]`, is Kunen's theorem as intended.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). K. Kunen, Elementary embeddings and infinitary combinatorics, J. Symbolic Logic 36 (1971), 407–413; stated as Theorem 1 in Hamkins, Kirmayer, Perlmutter (2012); A. Kanamori, The Higher Infinite, §23. Origin of this statement: the platform statement KunenZF.kunen_inconsistency_zfc is false as formalized (the empty structure is a model; verified disproof), and this is its corrected form with a nonempty structure.

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

set_option autoImplicit false

universe u

open FirstOrder FirstOrder.Language

namespace LefebvreVariations
theorem kunen_inconsistency_zfc_nonempty {M : Type u} [KunenZF.setLangJ.Structure M] [Nonempty M] :
    ¬ (M ⊨ KunenZF.zfcReinhardtTheory) := by sorry
end LefebvreVariations
