-- Prove2me | Theorems.Thm_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst
-- name    : MvFormalGroup.ArtinHasse.map_series_eq_map_exp_subst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/90c3c03f-ec76-585a-92c0-e89af27a0848
-- title:
--   Artin–Hasse series equals expbigl(sum_m X^{p^m}/p^mbigr)
-- statement:
--   Let $p$ be a prime. Recall the integral Artin–Hasse series [`MvFormalGroup.ArtinHasse.series p`](def/MvFormalGroup_ArtinHasse.html#L26) $\in \mathbb{Z}_p[\![X]\!]$, defined coefficientwise: its $k$-th coefficient is the $k$-th coefficient of the finite product `moebProd p k` of the series `moebFactor p n` taken over those $n$ with $0 < n \le k$ and $p \nmid n$ (so each coefficient is computed from a product truncated at the point beyond which further factors no longer affect it). On the other side, let $f \in \mathbb{Q}[\![X]\!]$ be the series whose $k$-th coefficient is $(k)^{-1} \in \mathbb{Q}$ when $k$ is a power of $p$, that is when $k = p^m$ for some $m \ge 0$, and $0$ otherwise; in particular $f$ has zero constant term, so the substitution of $f$ into Mathlib's exponential series `PowerSeries.exp ℚ` is defined. The theorem asserts an equality in $\mathbb{Q}_p[\![X]\!]$: the image of [`MvFormalGroup.ArtinHasse.series p`](def/MvFormalGroup_ArtinHasse.html#L26) under the coefficientwise map induced by $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$ equals the image under the coefficientwise map induced by $\mathbb{Q} \to \mathbb{Q}_p$ of $\exp \circ f$, i.e. of $\exp\bigl(\sum_{m \ge 0} X^{p^m}/p^m\bigr)$.
--
--   This is the classical Artin–Hasse identity, identifying the Möbius-product integral model of the Artin–Hasse exponential over $\mathbb{Z}_p$ with the exponential of $\sum_{m\ge 0} X^{p^m}/p^m$ over $\mathbb{Q}_p$; it shows in particular that the latter series has $p$-integral coefficients. It is used in the computation of logarithms of products $\prod_m E_p(x_m t^{p^m})$, and hence in the verification that the Artin–Hasse map is a morphism of multivariate formal groups, in [`MvFormalGroup.ArtinHasse.subst_addFam_fam`](thm.html#MvFormalGroup.ArtinHasse.subst_addFam_fam), [`MvFormalGroup.ArtinHasse.subst_addFam_map_coord`](thm.html#MvFormalGroup.ArtinHasse.subst_addFam_map_coord) and the corresponding statement for the big Witt law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst.lean

import Mathlib
import Definitions.Def_MvFormalGroup_ArtinHasse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical in

theorem MvFormalGroup.ArtinHasse.map_series_eq_map_exp_subst (p : ℕ) [Fact p.Prime] :
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (MvFormalGroup.ArtinHasse.series p) =
      PowerSeries.map (algebraMap ℚ ℚ_[p])
        ((PowerSeries.exp ℚ).subst
          (PowerSeries.mk fun k : ℕ => if ∃ m : ℕ, k = p ^ m then (k : ℚ)⁻¹ else 0)) := by sorry
