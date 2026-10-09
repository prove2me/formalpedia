-- Prove2me | Theorems.Thm_MPSTAsync_Progress_proposition_5_29_1
-- name    : MPSTAsync.Progress.proposition_5_29_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:17:31.739354+00:00
-- url     : https://prove2.me/theorems/3d9eec1f-e9e5-4b6e-a01a-cb0f37ae704d
-- title:
--   Proposition 5.29(1) — a nonterminated simple process has a step
-- statement:
--   Let a process $P$ have a simple runtime typing $\Gamma\vdash P\triangleright_{\widetilde s}\Delta$, with $\Delta$ coherent. Assume that $P$ is well-linked and that its queues are full relative to $\widetilde s$ and $\Delta$. If $P$ is not structurally congruent to inaction, it can reduce:
--
--   $$P\not\equiv 0\quad\Longrightarrow\quad\exists P'\; P\longrightarrow P'.$$
--
--   This is the immediate-step criterion used by the progress corollary.
--
--   **Formalization Note** Simplicity is relative to this particular typing derivation, as the proposition assumes. Well-formedness of $\Gamma$ records the paper's standing convention. Two hypotheses close a gap of the printed statement, which is false for open processes: every free name of $P$ has a shared sort $\langle G\rangle$ in $\Gamma$ (otherwise $\mathsf{if}\ x\ \mathsf{then}\ 0\ \mathsf{else}\ 0$ with $x:\mathsf{bool}$ is simple, typed by $\emptyset$ and stuck), and $P$ has no free process variables (otherwise a call $X\langle\rangle$ typed by [VAR] is stuck).
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, p. 37, Proposition 5.29 (1), https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Activity

set_option autoImplicit false

namespace MPSTAsync.Progress

theorem proposition_5_29_1 (Γ : Env) (hΓ : Γ.WellFormed)
    (P : Proc) (q : List Chan) (Δ : Typing)
    (hP : RTypedSimple Γ P q Δ)
    (hcoh : TypingCoherent Δ) (hwl : WellLinked P)
    (hq : QueueFull q Δ)
    (hshared : ∀ a ∈ P.freeNames, ∃ G, (a, ValSort.shared G) ∈ Γ.names)
    (hpvars : P.freePVars = ∅)
    (hne : ¬ Congr P .nil) :
    ∃ P', Reduces P P' := by sorry

end MPSTAsync.Progress
