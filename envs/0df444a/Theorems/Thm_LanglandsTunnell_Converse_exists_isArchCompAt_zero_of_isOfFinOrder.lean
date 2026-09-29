-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_zero_of_isOfFinOrder
-- name    : LanglandsTunnell.Converse.exists_isArchCompAt_zero_of_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/c15dc380-58f2-54ee-a729-c9b2d6d25771
-- title:
--   Finite-order idele characters have trivial infinity type
-- statement:
--   Let $K$ be a number field and let $\chi\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism from the units of the adele ring of $K$ to $\mathbb{C}^\times$, assumed continuous and of finite order, and let $w$ be an infinite place of $K$. The assertion is a conjunction of two implications about the archimedean component of $\chi$ at $w$, namely the character $x \mapsto \chi(\mathrm{archUnitHom}\,w\,x)$ of the units of the completion $K_w$ obtained by composing $\chi$ with the embedding `archUnitHom` of these local units into the idele group. First, if $w$ is real, then there is $a \in \mathbb{Z}/2$ such that the predicate `IsArchCompAt` holds with exponent $u = 0$ and integer $a.\mathrm{val}$, that is, for every unit $x$ of $K_w$ one has $\chi(\mathrm{archUnitHom}\,w\,x) = \lVert x\rVert^{\,w.\mathrm{mult}\cdot 0}\,(\mathrm{extensionEmbedding}\,w\,(x)/\lVert x\rVert)^{a.\mathrm{val}}$, so the component is the sign character raised to the power $a.\mathrm{val} \in \{0,1\}$. Second, if $w$ is complex, then `IsArchCompAt` holds with $u = 0$ and exponent $0$, i.e. $\chi(\mathrm{archUnitHom}\,w\,x) = 1$ for all units $x$ of $K_w$.
--
--   This is the classical statement that a finite-order Hecke character has trivial infinity type: its component at a real place is a power of the sign character and its component at a complex place is trivial. It supplies the archimedean local data used in the converse-theorem and cubic-induction steps of the Langlands–Tunnell argument, where the infinity type of a finite-order character and of its twists must be written explicitly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isArchCompAt_zero_of_isOfFinOrder.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_isArchCompAt_zero_of_isOfFinOrder
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ : Continuous χ) (hfin : IsOfFinOrder χ) (w : InfinitePlace K) :
    (w.IsReal → ∃ a : ZMod 2, IsArchCompAt K χ w 0 (a.val : ℤ)) ∧
    (w.IsComplex → IsArchCompAt K χ w 0 0) := by sorry
