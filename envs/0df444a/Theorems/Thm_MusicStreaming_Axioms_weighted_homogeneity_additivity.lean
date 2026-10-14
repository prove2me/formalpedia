-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_weighted_homogeneity_additivity
-- name    : MusicStreaming.Axioms.weighted_homogeneity_additivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:12.078659+00:00
-- url     : https://prove2.me/theorems/771c028f-3dc6-46b6-b59f-db8de84a98c3
-- title:
--   Appendix, proof of Theorem 1(a), p. 18 — every weighted index satisfies homogeneity and additivity
-- statement:
--   Let $\omega$ be a weight system: a function assigning to every user $j$ and every streaming profile $x\in\mathbb N^N$ a weight $\omega(j,x)>0$. Its weighted index is $I^\omega_i(N,M,t)=\sum_{j\in M}\omega(j,t_{\cdot j})\,t_{ij}$. Then
--   $$I^\omega \text{ satisfies homogeneity and additivity.}$$
--
--   This is the "if" direction of Theorem 1(a): each weighted index, and in particular the pro-rata and the user-centric index, satisfies the two basic axioms.
--
--   **Formalization Note** Additivity is over disjoint user sets, as in the definition module.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 18, Appendix, proof of Theorem 1(a), first paragraph

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem weighted_homogeneity_additivity {n : ℕ} (ω : ℕ → (Fin n → ℕ) → ℝ)
    (hω : ∀ j x, 0 < ω j x) :
    Homogeneity (weightedIndex ω) ∧ Additivity (weightedIndex ω) := by sorry

end MusicStreaming.Axioms
