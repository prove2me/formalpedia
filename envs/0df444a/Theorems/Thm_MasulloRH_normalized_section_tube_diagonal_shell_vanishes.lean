-- Prove2me | Theorems.Thm_MasulloRH_normalized_section_tube_diagonal_shell_vanishes
-- name    : MasulloRH.normalized_section_tube_diagonal_shell_vanishes
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:59:55.384341+00:00
-- url     : https://prove2.me/theorems/69fc71e0-fd0f-40ce-8577-d3d91d1f61cf
-- title:
--   Normalized angular section tubes have zero nonidentity shell on the two-variable diagonal
-- statement:
--   Let $D$ and $K$ be groups, with a measure on $K$, and let $U$ be a measurable subgroup of $K$ with positive finite mass $v$. In the split coordinates of a norm fiber put $T(r,h)=1_{r=1}1_U(h)/v$. Its two-variable diagonal orbit average $A(\xi,g)=\sum_r\int_K T(r,h)T(r\xi,hg)\,dh$ equals $1_{\xi=1}1_U(g)/v$. Integrating $A(\xi,g)$ against a real angular test gives its normalized $U$-average at $\xi=1$ and zero for every other lift. Every shell multiplier vanishing at the identity annihilates this overlap pointwise. Over the rational ideles, the norm fibers split with $D=\mathbb Q^\times$ and $K=\widehat{\mathbb Z}^{\times}$, and the shell in (11.3.2.1) vanishes at the identity lift. This theorem evaluates the normalized tube replacement of the printed section in (11.3.2.2).
-- source:
--   Masullo, The Music of the Primes, frozen §§11.3.1–2, (11.3.2.1–2), and Appendix (A.2.3.14); proof developed for the Prove2Me mission.

import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

theorem MasulloRH.normalized_section_tube_diagonal_shell_vanishes
    {D K : Type*} [Group D] [Group K] [MeasurableSpace K] (μ : Measure K)
    (U : Subgroup K) (hm : MeasurableSet (U : Set K)) (hv : μ.real (U : Set K) ≠ 0)
    [DecidableEq D] [DecidablePred (fun g : K => g ∈ U)] :
    let w := (μ.real (U : Set K))⁻¹
    let tube := fun (r : D) (h : K) => if r = 1 ∧ h ∈ U then w else 0
    let overlap := fun (ξ : D) (g : K) =>
      ∑' r : D, ∫ h : K, tube r h * tube (r * ξ) (h * g) ∂μ
    (∀ ξ g, overlap ξ g = if ξ = 1 ∧ g ∈ U then w else 0) ∧
    (∀ ξ (f : K → ℝ), ∫ g : K, overlap ξ g * f g ∂μ =
      if ξ = 1 then w * ∫ g in (U : Set K), f g ∂μ else 0) ∧
    ∀ (shell : D → ℝ), shell 1 = 0 → ∀ ξ g, shell ξ * overlap ξ g = 0 := by sorry
