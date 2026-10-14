-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_proRata_axioms
-- name    : MusicStreaming.Axioms.proRata_axioms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:13.263578+00:00
-- url     : https://prove2.me/theorems/49842caa-db6d-4e93-b79d-7dd9def0e205
-- title:
--   Appendix, proof of Theorem 1(b), p. 19 — pro-rata satisfies homogeneity, additivity and equal individual impact of similar users
-- statement:
--   The pro-rata index $P_i(N,M,t)=T_i=\sum_{j\in M}t_{ij}$ satisfies
--
--   1. homogeneity,
--   2. additivity, and
--   3. equal individual impact of similar users: whenever $j,j'\in M$ and $t_{ij}=t_{ij'}$,
--   $$P_i(N,M\setminus\{j\},t_{-j})=T_i-t_{ij}=T_i-t_{ij'}=P_i(N,M\setminus\{j'\},t_{-j'}).$$
--
--   This is the "if" direction of Theorem 1(b).
--
--   **Formalization Note** The proof on p. 19 prints $T_i(N,M,t^{-j})-t_{ij}$ where $T_i(N,M,t)-t_{ij}$ is meant; only the conclusion is formalized.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 19, Appendix, proof of Theorem 1(b), first paragraph

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem proRata_axioms {n : ℕ} :
    Homogeneity (proRata (n := n)) ∧ Additivity (proRata (n := n)) ∧
      EqualIndividualImpact (proRata (n := n)) := by sorry

end MusicStreaming.Axioms
