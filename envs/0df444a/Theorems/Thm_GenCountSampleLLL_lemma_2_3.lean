-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_2_3
-- name    : GenCountSampleLLL.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:53:11.691192+00:00
-- url     : https://prove2.me/theorems/89ed6c62-2645-4903-adb3-bf9c07177c46
-- title:
--   Lemma 2.3, p.8 — the selection procedure outputs exactly $\mathfrak T_{\mathcal D,a}$, its fibres, and $\mathcal F(\mathcal T)=\mathcal F_1(\mathcal T)\sqcup\mathcal D_{\mathcal T}$
-- statement:
--   Let $a\in\mathcal D\subseteq\mathcal C$. The possible outputs of the selection procedure (on inputs $\mathcal B\subseteq\mathcal D$ with $a\in\mathcal B$) are exactly the rooted 2-trees $\mathcal T\in\mathfrak T_{\mathcal D,a}$. For each such $\mathcal T$,
--   $$
--   \{\mathcal B\subseteq\mathcal D:a\in\mathcal B,\ \mathrm{Tree}_{\mathcal D,a}(\mathcal B)=\mathcal T\}=\{\mathcal T\cup\mathcal W:\mathcal W\subseteq\mathcal F(\mathcal T)\},
--   $$
--   and $\mathcal F(\mathcal T)=\mathcal F_1(\mathcal T)\sqcup\mathcal D_{\mathcal T}$ is a disjoint union.
--
--   This lemma groups the inclusion–exclusion expansion of $\mathbf 1_{B_a}\mathbf 1_{\mathrm{Good}(\mathcal D^-)}$ by selected trees.
--
--   Differences from the source:
--   - generalization: stated under the standing assumption (1.1) with c = 1/100 (§2, p.7) → stated for every instance, without (1.1); reason: the statement is combinatorial and does not use (1.1); adding the hypothesis gives the source's statement
--   - reading: "the possible outputs … are exactly the elements of 𝔗_{𝒟,a}" → two conjuncts: every output on an input ℬ ⊆ 𝒟 with a ∈ ℬ is a rooted 2-tree, and every rooted 2-tree is the output on some such input; reason: both inclusions of "exactly"
--   - encoding: "the first constraint"; ℱ(𝒯) = ℱ₁(𝒯) ⊔ 𝒟_𝒯 → the least constraint in the order of `Fin m`; the union stated with disjointness; reason: the fixed ordering of p.7; ⊔ is a disjoint union
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 2.3, p.8

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Lemma 2.3, p.8 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)). For `a ∈ D ⊆ C`: the possible outputs of the selection
procedure (on inputs `B ⊆ D` with `a ∈ B`) are exactly the rooted 2-trees `T ∈ T_{D,a}`; for each
such `T`, `{B ⊆ D : a ∈ B, Tree_{D,a}(B) = T} = {T ∪ W : W ⊆ F(T)}`; and `F(T) = F₁(T) ⊔ D_T`
(a disjoint union).

**Formalization Note.** The lemma is combinatorial and holds for every instance; the standing
assumption (1.1) is not used and not assumed. -/
theorem lemma_2_3 (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    (∀ B ⊆ D, a ∈ B → I.Tree D a B ∈ I.twoTrees D a) ∧
    (∀ T ∈ I.twoTrees D a, ∃ B ⊆ D, a ∈ B ∧ I.Tree D a B = T) ∧
    (∀ T ∈ I.twoTrees D a,
      D.powerset.filter (fun B => a ∈ B ∧ I.Tree D a B = T) =
        (I.Fset D a T).powerset.image (fun W => T ∪ W)) ∧
    (∀ T ∈ I.twoTrees D a,
      I.Fset D a T = I.F1 D a T ∪ I.DT D T ∧ Disjoint (I.F1 D a T) (I.DT D T)) := by sorry

end GenCountSampleLLL
