-- Prove2me | Theorems.Thm_Moise_theta_curve_separation
-- name    : Moise.theta_curve_separation
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T21:34:50.645803+00:00
-- url     : https://prove2.me/theorems/7ec20926-2f7e-418a-9b56-f840f3f1543f
-- title:
--   Theta-curve separation theorem in $\mathbb{R}^2$
-- statement:
--   Let $\alpha_1, \alpha_2, \alpha_3 : [0,1] \to \mathbb{R}^2$ be three topological arcs sharing the same endpoints $\alpha_1(0) = \alpha_2(0) = \alpha_3(0)$ and $\alpha_1(1) = \alpha_2(1) = \alpha_3(1)$, whose open interiors $\alpha_i((0,1))$ are pairwise disjoint (a $\theta$-curve). Then $\mathbb{R}^2 \setminus (\alpha_1([0,1]) \cup \alpha_2([0,1]) \cup \alpha_3([0,1]))$ is the disjoint union of three open connected components $U_1, U_2, U_3$.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 4.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic

namespace Moise

theorem theta_curve_separation
    (α₁ α₂ α₃ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (h₁ : Continuous α₁) (h₂ : Continuous α₂) (h₃ : Continuous α₃)
    (hinj₁ : Function.Injective α₁) (hinj₂ : Function.Injective α₂) (hinj₃ : Function.Injective α₃)
    (h0₁₂ : α₁ ⟨0, by norm_num⟩ = α₂ ⟨0, by norm_num⟩)
    (h0₂₃ : α₂ ⟨0, by norm_num⟩ = α₃ ⟨0, by norm_num⟩)
    (h1₁₂ : α₁ ⟨1, by norm_num⟩ = α₂ ⟨1, by norm_num⟩)
    (h1₂₃ : α₂ ⟨1, by norm_num⟩ = α₃ ⟨1, by norm_num⟩)
    (hdisj₁₂ : Disjoint (α₁ '' Set.Ioo ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)
      (α₂ '' Set.Ioo ⟨0, by norm_num⟩ ⟨1, by norm_num⟩))
    (hdisj₂₃ : Disjoint (α₂ '' Set.Ioo ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)
      (α₃ '' Set.Ioo ⟨0, by norm_num⟩ ⟨1, by norm_num⟩))
    (hdisj₁₃ : Disjoint (α₁ '' Set.Ioo ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)
      (α₃ '' Set.Ioo ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)) :
    ∃ U₁ U₂ U₃ : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U₁ ∧ IsOpen U₂ ∧ IsOpen U₃ ∧
      _root_.IsConnected U₁ ∧ _root_.IsConnected U₂ ∧ _root_.IsConnected U₃ ∧
      Disjoint U₁ U₂ ∧ Disjoint U₂ U₃ ∧ Disjoint U₁ U₃ ∧
      U₁ ∪ U₂ ∪ U₃ = (Set.range α₁ ∪ Set.range α₂ ∪ Set.range α₃)ᶜ := by sorry

end Moise
