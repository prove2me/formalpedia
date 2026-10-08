-- Prove2me | Theorems.Thm_HallReps_CDR_card_lt_of_subset_cdrMeet
-- name    : HallReps.CDR.card_lt_of_subset_cdrMeet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:08:57.148544+00:00
-- url     : https://prove2.me/theorems/f8fb50d9-97f1-45ae-b713-a3509dca5206
-- title:
--   p. 29, proof of Theorem 1 — if T_m ⊆ R*, the ρ+1 sets T_1, …, T_ρ, T_m contain between them only the ρ elements of R*
-- statement:
--   Let $T_1, \dots, T_m$ ($m \ge 1$) be subsets of a set $S$ and suppose the system
--   $$T_1, T_2, \dots, T_{m-1} \tag{4}$$
--   has a C.D.R. Let $R^*$ be the meet of all the C.D.R.s of (4), and write $\rho = |R^*|$. If
--   $$T_m \subseteq R^*,$$
--   then $R^*$ is finite and there are $k = \rho + 1$ of the sets — namely $T_m$ together with the $\rho$ sets $T_1, \dots, T_\rho$ represented by the elements of $R^*$ — which contain between them only the $\rho$ elements of $R^*$: there is a set $J$ of indices with $m \in J$, $|J| = \rho + 1$ and
--   $$\bigcup_{j \in J} T_j = R^*.$$
--
--   This is the second half of the induction step in Hall's proof of Theorem 1: it exhibits $\rho + 1$ sets with only $\rho$ elements between them, contradicting the hypothesis of Theorem 1.
--
--   **Formalization Note.** Indexing as in the companion step: the paper's $m$ sets are `T : Fin (m + 1) → Set α`, (4) is `fun i : Fin m => T i.castSucc`, $T_m$ is `T (Fin.last m)`. The C.D.R. `b` of (4) is a hypothesis, as on the page (without one, $R^*$ would be all of $S$). The count is stated with `Set.ncard` together with the finiteness of $R^*$, so the junk value of `ncard` on an infinite set cannot occur.
-- source:
--   P. Hall, On representatives of subsets, J. London Math. Soc. 10 (1935), p. 29, proof of Theorem 1 (first paragraph)

import Mathlib
import Definitions.Def_HallReps_CDR_System

namespace HallReps.CDR

theorem card_lt_of_subset_cdrMeet {α : Type*} {m : ℕ} (T : Fin (m + 1) → Set α)
    (b : Fin m → α) (hb : IsCDR (fun i : Fin m => T i.castSucc) b)
    (hT : T (Fin.last m) ⊆ cdrMeet (fun i : Fin m => T i.castSucc)) :
    ∃ s : Finset (Fin (m + 1)), Fin.last m ∈ s ∧
      (⋃ i ∈ s, T i) = cdrMeet (fun i : Fin m => T i.castSucc) ∧
      (cdrMeet (fun i : Fin m => T i.castSucc)).Finite ∧
      s.card = (cdrMeet (fun i : Fin m => T i.castSucc)).ncard + 1 := by sorry

end HallReps.CDR
