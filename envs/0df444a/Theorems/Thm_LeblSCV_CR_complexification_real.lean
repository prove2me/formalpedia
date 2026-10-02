-- Prove2me | Theorems.Thm_LeblSCV_CR_complexification_real
-- name    : LeblSCV.CR.complexification_real
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:36:25.073981+00:00
-- url     : https://prove2.me/theorems/6c218b97-74c3-4d48-9341-c711badeacb2
-- title:
--   Proposition 3.1.3 — complexification of a real-analytic function on a domain of $\mathbb{R}^n$
-- statement:
--   Let $U \subset \mathbb{R}^n$ be a domain and $f : U \to \mathbb{C}$ real-analytic, and regard $\mathbb{R}^n \subset \mathbb{C}^n$ through the natural inclusion. Then there exist a domain $V \subset \mathbb{C}^n$ with $U \subset V$ and a unique holomorphic function $F : V \to \mathbb{C}$ with
--   $$F|_U = f.$$
--   Uniqueness is for the found $V$: any holomorphic $G$ on $V$ with $G|_U = f$ equals $F$ on $V$. As a consequence every real-analytic function is $C^\infty$.
--
--   **Formalization Note.** $U$ is `Set (Fin n → ℝ)`, a domain means `IsOpen ∧ IsConnected`, real-analytic is `IsRealAnalyticOn` (Definition 3.1.1), holomorphic is `DifferentiableOn ℂ`, and $U \subset V$ means `realEmbed '' U ⊆ V`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 105, Proposition 3.1.3

import Mathlib
import Definitions.Def_LeblSCV_CR_IsRealAnalyticOn
import Definitions.Def_LeblSCV_CR_realEmbed

namespace LeblSCV.CR

/-- Proposition 3.1.3 (Complexification part I; Lebl, p. 105): if `U ⊂ ℝⁿ` is a domain and
`f : U → ℂ` is real-analytic, then there is a domain `V ⊂ ℂⁿ` with `U ⊂ V` (via the natural
inclusion `ℝⁿ ⊂ ℂⁿ`) and a unique holomorphic `F : V → ℂ` with `F|_U = f`. -/
theorem complexification_real {n : ℕ} (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hUc : IsConnected U) (f : (Fin n → ℝ) → ℂ) (hf : IsRealAnalyticOn U f) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ IsConnected V ∧ realEmbed '' U ⊆ V ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F V ∧ (∀ x ∈ U, F (realEmbed x) = f x) ∧
        ∀ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V → (∀ x ∈ U, G (realEmbed x) = f x) →
          Set.EqOn G F V := by sorry

end LeblSCV.CR
