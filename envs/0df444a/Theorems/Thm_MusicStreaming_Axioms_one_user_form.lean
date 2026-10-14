-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_one_user_form
-- name    : MusicStreaming.Axioms.one_user_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:19.623425+00:00
-- url     : https://prove2.me/theorems/8a752380-ade0-4eb3-9fbe-010d9bef96fe
-- title:
--   Appendix, proof of Theorem 1(a), pp. 18–19 — on a one-user problem a homogeneous index is proportional to the profile
-- statement:
--   Let $I$ be an index satisfying homogeneity, let $j$ be a user and let $x\in\mathbb N^N$ be a nonzero streaming profile. On the one-user problem $(N,\{j\},x)$, for every artist $i$,
--   $$I_i(N,\{j\},x)=\frac{\sum_{i'\in N}I_{i'}(N,\{j\},x)}{T^j(N,\{j\},x)}\;x_i,\qquad T^j(N,\{j\},x)=\sum_{i'\in N}x_{i'} .$$
--
--   Together with the additive decomposition this produces the weight system $\omega(j,x)=\sum_{i'}I_{i'}(N,\{j\},x)/T^j$ representing an index that satisfies both axioms.
--
--   **Formalization Note** The profile is required to be nonzero: a user of a problem always played some artist (the paper recalls this "basic assumption" on p. 19), and it keeps $T^j>0$.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, pp. 18–19, Appendix, proof of Theorem 1(a), display "Hence, I_i(N,{j},t.j) = …" (p. 19)

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem one_user_form {n : ℕ} (I : Index n) (hH : Homogeneity I) :
    ∀ (j : ℕ) (x : Fin n → ℕ), x ≠ 0 → ∀ i : Fin n,
      I (Finsupp.single j x) i =
        (∑ i', I (Finsupp.single j x) i') / (∑ i', (x i' : ℝ)) * x i := by sorry

end MusicStreaming.Axioms
