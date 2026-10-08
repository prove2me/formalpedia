-- Prove2me | Theorems.Thm_HallReps_CDR_cdr_of_not_subset_cdrMeet
-- name    : HallReps.CDR.cdr_of_not_subset_cdrMeet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:08:40.019215+00:00
-- url     : https://prove2.me/theorems/773f0f01-8453-42c0-9c3b-8df1fd22a128
-- title:
--   p. 28, proof of Theorem 1 — (1) has a C.D.R. provided T_m is not contained in the meet of all C.D.R.s of (4)
-- statement:
--   Let $T_1, \dots, T_m$ ($m \ge 1$) be subsets of a set $S$, and consider the shorter system
--   $$T_1, T_2, \dots, T_{m-1} \tag{4}$$
--   obtained by deleting the last set. Let $R^*$ be the meet of all the C.D.R.s of (4): the set of elements of $S$ occurring as representatives in every C.D.R. of (4). If $T_m$ is not contained in $R^*$,
--   $$T_m \not\subseteq R^*,$$
--   then the full system $T_1, \dots, T_m$ has a C.D.R.
--
--   This is the first half of the induction step in Hall's proof of Theorem 1: an element $a_m \in T_m \setminus R^*$ is avoided by some C.D.R. of (4), and that C.D.R. together with $a_m$ represents the whole system.
--
--   **Formalization Note.** The paper's $m$ sets are `T : Fin (m + 1) → Set α` (so the Lean `m + 1` is the paper's $m$, and $m \ge 1$ is built in); the system (4) is `fun i : Fin m => T i.castSucc` and $T_m$ is `T (Fin.last m)`. The paper also has, at this point, a C.D.R. of (4) from the induction hypothesis; it is not assumed here because the hypothesis $T_m \not\subseteq R^*$ already implies it (if (4) had no C.D.R., $R^*$ would be all of $S$).
-- source:
--   P. Hall, On representatives of subsets, J. London Math. Soc. 10 (1935), pp. 28–29, proof of Theorem 1 (last paragraph of p. 28 and first paragraph of p. 29)

import Mathlib
import Definitions.Def_HallReps_CDR_System

namespace HallReps.CDR

theorem cdr_of_not_subset_cdrMeet {α : Type*} {m : ℕ} (T : Fin (m + 1) → Set α)
    (hT : ¬ T (Fin.last m) ⊆ cdrMeet (fun i : Fin m => T i.castSucc)) :
    ∃ a : Fin (m + 1) → α, IsCDR T a := by sorry

end HallReps.CDR
