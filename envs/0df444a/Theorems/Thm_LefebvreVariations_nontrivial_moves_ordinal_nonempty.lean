-- Prove2me | Theorems.Thm_LefebvreVariations_nontrivial_moves_ordinal_nonempty
-- name    : LefebvreVariations.nontrivial_moves_ordinal_nonempty
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:11:49.494865+00:00
-- url     : https://prove2.me/theorems/f61b43c5-35a1-4f78-88d4-bae9068fc999
-- title:
--   Lefebvre's variations, No. 242 — on a theme by Hamkins and Kirmayer: in ZF(j) a nontrivial elementary embedding V → V moves an ordinal (nonempty models)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Work in the first-order language $\{\in, j\}$ with $j$ a unary function symbol. Let $\mathrm{ZF}(j)$ be ZF with Separation and Collection for all $\{\in,j\}$-formulas, and let $j$ satisfy the elementarity scheme $\varphi(\bar x) \leftrightarrow \varphi(j\bar x)$ for every pure $\in$-formula $\varphi$. Then the sentence
--
--   $$\forall x\ \big(x \text{ is an ordinal} \to j(x) = x\big) \;\wedge\; \exists x\ j(x) \neq x$$
--
--   has no model: if $j : V \to V$ is a nontrivial elementary embedding then $j$ moves some ordinal. Equivalently $j$ has a critical point (a Reinhardt cardinal). This is Hamkins–Kirmayer–Perlmutter, *Generalizations of the Kunen inconsistency*, Lemma 4(2) (case $N \subseteq M$, $M=N=V$), provable in $\mathrm{ZF}(j)$ without Choice.
--
--   Proof idea: if $j$ fixes all ordinals then $j$ preserves rank, and by $\in$-induction on rank $j(x)=x$ for all $x$: $y\in x \Rightarrow y = j(y) \in j(x)$, and $z\in j(x)$ has rank below $\mathrm{rk}(j(x)) = \mathrm{rk}(x)$, so $z=j(z)$ by induction, hence $z \in x$ by elementarity.
--
--   **Formalization Note** Models are `M : Type u` with a `setLangJ`-structure, `M ⊨ T` is Mathlib's `FirstOrder.Language.Theory.Model`, and `reinhardtTheory`, `fixesOrdinalsFormula` come from the platform definitions `Definitions.Def_KunenZF_theory`. The only change from the platform statement `KunenZF.nontrivial_moves_ordinal` is the added binder `[Nonempty M]`. Why a corrected statement: in the platform formalization `KunenZF.nontrivial_moves_ordinal` the structure `M : Type u` is not required to be nonempty. The empty structure (with `j` and `∈` interpreted vacuously) satisfies every sentence of the form `close φ` / `closeJ φ`, because these quantify over `Fin (n+1) → M`, a type with no element when `M` is empty; all axioms of `reinhardtTheory`, of `zfcReinhardtTheory` and of `reinhardtDefinableTheory δ` are of this form, so the empty structure is a model of each and the four platform statements `KunenZF.kunen_inconsistency_zf`, `kunen_inconsistency_zfc`, `nontrivial_moves_ordinal`, `suzuki_no_definable_reinhardt` are false as formalized (Lean-verified disproofs, axioms `propext, Classical.choice, Quot.sound`). The statement below adds the binder `[Nonempty M]`, which is what first-order logic assumes; it is the intended statement.
--
--   **Why this is a Lefebvre variation.** It is the corrected form of the open platform statement `KunenZF.nontrivial_moves_ordinal`, which is false as formalized: the empty structure is a model of `reinhardtTheory ∪ {closeJ fixesOrdinalsFormula}` (Lean-verified disproof). Hence no Lean-verified reduction of the original exists; this statement, with the added hypothesis `[Nonempty M]`, is the theorem that was intended, and it is a known ZF theorem (a special case of the statement behind the original).
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). Hamkins, Kirmayer, Perlmutter, Generalizations of the Kunen inconsistency, Ann. Pure Appl. Logic 163 (2012), 1872–1890, Lemma 4(2). Origin of this statement: the platform statement KunenZF.nontrivial_moves_ordinal is false as formalized (the empty structure is a model; verified disproof), and this is its corrected form with a nonempty structure.

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

set_option autoImplicit false

universe u

open FirstOrder FirstOrder.Language

namespace LefebvreVariations
theorem nontrivial_moves_ordinal_nonempty {M : Type u} [KunenZF.setLangJ.Structure M] [Nonempty M] :
    ¬ (M ⊨ (KunenZF.reinhardtTheory ∪ {KunenZF.SFormulaJ.closeJ KunenZF.fixesOrdinalsFormula})) := by sorry
end LefebvreVariations
