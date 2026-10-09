-- Prove2me | Theorems.Thm_MPSTAsync_Progress_corollary_5_30
-- name    : MPSTAsync.Progress.corollary_5_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:18:43.500662+00:00
-- url     : https://prove2.me/theorems/86b68a94-38a3-48d1-bd3c-15d9e752cfb1
-- title:
--   Corollary 5.30 — progress of a simple, well-linked program
-- statement:
--   Let $P$ be a **program** in the sense of Definition 2.1: up to structural congruence it has no queues or restricted session channels and has no free session channels or process variables. Suppose $P$ is simple, meaning that it admits a restricted well-formed typing derivation, and well-linked, meaning that every reachable active shared-name prefix belongs to a redex. Assume also that its free names have shared sorts (no free Boolean variables). Then every process $P'$ reachable from $P$ either is structurally congruent to inaction or takes another reduction step:
--
--   $$P\longrightarrow^*P'\quad\Longrightarrow\quad P'\equiv 0\quad\lor\quad\exists P''\;P'\longrightarrow P''.$$
--
--   The result rules out stuck intermediate states for this class of multiparty asynchronous programs.
--
--   **Formalization Note** The existential typing witness is part of `Simple`; no separate typing hypothesis is added. The endpoint of a completed restricted session is compared with $0$ by structural congruence, which removes empty queues. One hypothesis closes a gap of the printed statement: some simple typing gives every free name of $P$ a shared sort $\langle G\rangle$. A program may keep free names, and with $x:\mathsf{bool}$ the program $\mathsf{if}\ x\ \mathsf{then}\ 0\ \mathsf{else}\ 0$ is simple, well-linked and stuck, because $x$ evaluates to no Boolean.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, p. 37, Corollary 5.30, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Activity

set_option autoImplicit false

namespace MPSTAsync.Progress

theorem corollary_5_30 (P : Proc) (hprog : IsProgram P)
    (hsimple : Simple P) (hwl : WellLinked P)
    (hshared : ∃ Γ q Δ, Γ.WellFormed ∧ RTypedSimple Γ P q Δ ∧
      ∀ a ∈ P.freeNames, ∃ G, (a, ValSort.shared G) ∈ Γ.names) :
    ∀ P', Relation.ReflTransGen Reduces P P' →
      Congr P' .nil ∨ ∃ P'', Reduces P' P'' := by sorry

end MPSTAsync.Progress
