-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_weighted_class_bound
-- name    : OAI.TwoWayComplementation.weighted_class_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:28:28.969915+00:00
-- url     : https://prove2.me/theorems/c1e9d4fc-2b6f-4c8e-aab1-9fed6887f9c4
-- title:
--   A weighted counting bound: if every element of $Y$ owns an unmarked point or two points of $X$, then $2|Y|+|M|\le2|X|$
-- statement:
--   Let $X$ and $M$ be finite subsets of a set $\alpha$ with $M\subseteq X$, let $Y$ be a finite subset of a set $\beta$, and let $R\subseteq\beta\times\alpha$ be a relation; say that $y$ *owns* $x$ if $(y,x)\in R$, and call the points of $M$ *marked*. Write $|\cdot|$ for cardinality. Assume:
--
--   1. (Disjointness) every $x\in X$ is owned by at most one element of $Y$: if $y,y'\in Y$, $x\in X$, and both $y$ and $y'$ own $x$, then $y=y'$;
--   2. (Covering) every $y\in Y$ owns some unmarked point $x\in X\setminus M$, or owns two distinct elements $x\neq x'$ of $X$.
--
--   Then
--   $$2\,|Y|+|M|\le 2\,|X| .$$
--
--   Equivalently $|Y|\le|X|-\tfrac12|M|$: marked points count only half, because an element of $Y$ owning only marked points must own at least two of them. In the lower-bound argument, $X$ is the set of unprotected recurrent classes of an idempotent boundary diagram $e$, $M$ is the set of classes of $e$ missing in a nested idempotent $d$ (all assumed unprotected), $Y$ is the set of unprotected classes of $d$, and a class of $d$ owns the classes of $e$ of the same sign that it contains. The inequality $2|Y|+|M|\le2|X|$ then bounds the total number of classes lost along a chain of nested idempotents.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean#L257-L315

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.weighted_class_bound {α β : Type*} (X M : Finset α) (Y : Finset β)
    (R : β → α → Prop) (hM : M ⊆ X)
    (hunique : ∀ y ∈ Y, ∀ z ∈ Y, ∀ x ∈ X, R y x → R z x → y = z)
    (hcover : ∀ y ∈ Y,
      (∃ x ∈ X, x ∉ M ∧ R y x) ∨
        ∃ x ∈ X, ∃ z ∈ X, x ≠ z ∧ R y x ∧ R y z) :
    2 * Y.card + M.card ≤ 2 * X.card := by sorry
