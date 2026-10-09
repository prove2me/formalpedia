-- Prove2me | Theorems.Thm_MPSTAsync_Progress_theorem_5_22
-- name    : MPSTAsync.Progress.theorem_5_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:20:25.466978+00:00
-- url     : https://prove2.me/theorems/f44de857-46a8-44b7-8605-68985be359b2
-- title:
--   Theorem 5.22 — communication safety
-- statement:
--   Suppose $\Gamma\vdash P\triangleright_{\widetilde t}\Delta$, the session typing $\Delta$ is coherent, and $P$ has a redex at a free session channel $s$. First, the queue at $s$ is unique and the active prefixes at $s$ have one of the three forms stated in the paper: one receiving prefix with a nonempty queue, one emitting prefix, or one of each. Second, a value input, delegated-channel input or branch selection has a queue-head message of the corresponding kind, with matching vector length or offered label.
--
--   $$\text{coherent typing and a redex at }s\quad\Longrightarrow\quad\text{linearity and message-kind agreement at }s.$$
--
--   This theorem is the communication-safety input to Proposition 5.29.
--
--   **Formalization Note** $\Gamma$ is well formed by the section's standing convention. The notation $P\equiv E[R]$ uses structural congruence and a one-hole reduction context. An occurrence of $s$ in $E$ means any free occurrence outside its hole, including queue names and transmitted channels. The redex predicate requires $s$ to be free and identifies a firing session rule; the receiving part in clause (2) must participate in that redex.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, p. 35, Theorem 5.22, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Activity

set_option autoImplicit false

namespace MPSTAsync.Progress

theorem theorem_5_22 (Γ : Env) (hΓ : Γ.WellFormed) (P : Proc)
    (q : List Chan) (Δ : Typing) (c : Chan)
    (hP : RTyped true Γ P q Δ) (hcoh : TypingCoherent Δ)
    (hred : HasRedexAt P c) :
    (∃ (E : Ctx) (h : List Msg), Congr P (E.fill (.queue c h)) ∧
      ((ActiveRecv P c ∧ E.occ c = 1 ∧ h ≠ []) ∨
       (ActiveEmit P c ∧ E.occ c = 1) ∨
       (ActiveRecv P c ∧ ActiveEmit P c ∧ E.occ c = 2))) ∧
    (∀ (E : Ctx) (R : Proc), Congr P (E.fill R) → ReceivingRedexPart P R c →
      ((∀ (xs : List Name) (Q : Proc), Congr R (.recv c xs Q) →
          ∃ (E' : Ctx) (vs : List Val) (h : List Msg),
            Congr P (E'.fill (.queue c (.vals vs :: h))) ∧ vs.length = xs.length) ∧
       (∀ (ss : List Chan) (Q : Proc), Congr R (.srecv c ss Q) →
          ∃ (E' : Ctx) (ts : List Chan) (h : List Msg),
            Congr P (E'.fill (.queue c (.chans ts :: h))) ∧ ts.length = ss.length) ∧
       (∀ (bs : List (Label × Proc)), Congr R (.branch c bs) →
          ∃ (E' : Ctx) (l : Label) (Q : Proc) (h : List Msg),
            (l,Q) ∈ bs ∧ Congr P (E'.fill (.queue c (.label l :: h)))))) := by sorry

end MPSTAsync.Progress
