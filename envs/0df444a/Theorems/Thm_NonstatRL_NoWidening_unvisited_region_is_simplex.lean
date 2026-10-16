-- Prove2me | Theorems.Thm_NonstatRL_NoWidening_unvisited_region_is_simplex
-- name    : NonstatRL.NoWidening.unvisited_region_is_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:50.808027+00:00
-- url     : https://prove2.me/theorems/dbdbcd86-9a6e-4fe0-833e-341bf19b1bf3
-- title:
--   Proof of Lemma 13, first case — the unvisited transition region contains the simplex
-- statement:
--   Fix a finite state space with at least two states, nonempty allowed action sets, a horizon $T\ge1$, and $0<\delta<1$. For an allowed state-action pair $(s,a)$ with no visits in the chosen window, the transition radius satisfies
--
--   $$\operatorname{rad}_p(s,a)\ge1,$$
--
--   and every probability distribution on the states belongs to the unwidened confidence region $H_p(s,a;0)$.
--
--   This is the first case in the authors' construction of a transition model inside the region.
--
--   **Formalization Note** A zero count gives $N^+=1$ and empirical center $\hat p=0$. The hypotheses $S>1$ and $0<\delta<1$ are explicit pins needed for the printed radius claim. The window uses zero-based half-open indices.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 50, proof of Lemma 13, first case

import Mathlib
import Definitions.Def_NonstatRL_PerStep_Window

open BanditAlgorithm

namespace NonstatRL.NoWidening

theorem unvisited_region_is_simplex {S A : ℕ} (hS : 1 < S)
    (As : Fin S → Finset (Fin A)) (hAs : ∀ s, (As s).Nonempty)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (hzero : NonstatRL.PerStep.count st ac lo hi s a = 0) :
    1 ≤ NonstatRL.PerStep.radP As T δ (NonstatRL.PerStep.countPlus st ac lo hi s a) ∧
      ∀ p : Fin S → ℝ, (∀ s', 0 ≤ p s') → (∑ s', p s') = 1 →
        p ∈ NonstatRL.PerStep.Hp As T δ st ac lo hi 0 s a := by sorry

end NonstatRL.NoWidening
