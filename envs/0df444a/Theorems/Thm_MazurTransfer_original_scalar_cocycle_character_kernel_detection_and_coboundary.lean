-- Prove2me | Theorems.Thm_MazurTransfer_original_scalar_cocycle_character_kernel_detection_and_coboundary
-- name    : MazurTransfer.original_scalar_cocycle_character_kernel_detection_and_coboundary
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T13:34:17.451373+00:00
-- url     : https://prove2.me/theorems/128b605d-c106-49c6-b1aa-e7016c08ae67
-- statement:
--   Let $k$ be a field, $G$ a group, $\chi:G\to k^\times$, and $c:G\to k$ satisfy $c(gh)=c(g)+\chi(g)c(h)$ and vanish on $\ker\chi$. Then $c$ is constant on every fibre of $\chi$, satisfies $(\chi(g)-1)c(h)=(\chi(h)-1)c(g)$, and has the form $c(g)=\chi(g)a-a$ for some $a\in k$. Both original hypotheses are retained for arbitrary groups and fields. Named downstream consumer: restriction of the original scalar-character continuous cohomology classes to genuine characters of the same character kernel.

import Mathlib
noncomputable section

theorem MazurTransfer.original_scalar_cocycle_character_kernel_detection_and_coboundary : (∀ {k G : Type} [Field k] [Group G] (χ : G →* kˣ) (c : G → k) (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h) (hzero : ∀ g, χ g = 1 → c g = 0) (g h : G) (he : χ g = χ h), c g = c h) ∧ (∀ {k G : Type} [Field k] [Group G] (χ : G →* kˣ) (c : G → k) (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h) (hzero : ∀ g, χ g = 1 → c g = 0) (g h : G), ((χ g : k) - 1) * c h = ((χ h : k) - 1) * c g) ∧ (∀ {k G : Type} [Field k] [Group G] (χ : G →* kˣ) (c : G → k) (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h) (hzero : ∀ g, χ g = 1 → c g = 0), ∃ a : k, ∀ g, c g = (χ g : k) * a - a) := by sorry
