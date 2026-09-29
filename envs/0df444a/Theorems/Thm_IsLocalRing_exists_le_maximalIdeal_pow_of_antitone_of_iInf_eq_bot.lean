-- Prove2me | Theorems.Thm_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
-- name    : IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/ac8f63d7-4d90-505e-beab-90262e9a1311
-- title:
--   Chevalley's lemma on separated decreasing filtrations
-- statement:
--   Let $A$ be a commutative ring in a fixed universe which is Noetherian, local (with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal A`), and complete and separated for the $\mathfrak m$-adic filtration in the sense of Mathlib's `IsAdicComplete` for the ideal $\mathfrak m$. Let $K : \mathbb N \to$ `Ideal A` be a family of ideals of $A$ that is antitone, i.e. $K_v \supseteq K_w$ whenever $v \le w$, and suppose that the infimum of the $K_w$ is the zero ideal, $\bigcap_{w} K_w = \bot$. Then for every natural number $N$ there exists an index $w$ with $K_w \subseteq \mathfrak m^N$.
--
--   This is Chevalley's lemma: a separated decreasing filtration of a complete Noetherian local ring by ideals defines a topology at least as fine as the $\mathfrak m$-adic one. It is used in the construction of hulls of deformation functors and in the analysis of cotangent spaces of $p$-divisible groups over Artinian rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : ℕ → Ideal A) (hK : Antitone K) (hinf : ⨅ w, K w = ⊥) (N : ℕ) :
    ∃ w : ℕ, K w ≤ IsLocalRing.maximalIdeal A ^ N := by sorry
