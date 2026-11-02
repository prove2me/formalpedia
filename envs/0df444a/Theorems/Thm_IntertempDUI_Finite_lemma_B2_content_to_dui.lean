-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_B2_content_to_dui
-- name    : IntertempDUI.Finite.lemma_B2_content_to_dui
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T16:15:10.536772+00:00
-- url     : https://prove2.me/theorems/411c5ae7-7344-4ecf-a742-1fd8a5f6f313
-- title:
--   Nonatomic full-support content-utility representation ⟹ DUI representation
-- statement:
--   Let $T>0$ and let $\mathcal X$ be connected. Let $\mathcal A\subseteq C([0,T],\mathcal X)$ contain the constant trajectories. Let $\{\succsim_I\}$ satisfy the standing assumptions (each $\succsim_I$ is complete, transitive, nontrivial and depends only on restrictions to $I$).
--
--   Suppose $(u,\mu)$ is a content-utility representation (B6), where $\mu$ is a nonatomic content with full support on the time spans of $[0,T]$. Then there is a function $\rho$ with the following properties:
--
--   1. $\rho$ is continuous and $\rho(0)=0$, $\rho(T)=1$.
--   2. $\rho$ is strictly increasing on $[0,T]$.
--   3. $(\rho,u)$ is a discounted utility integral representation (8): for every time span $S$ (and every time interval)
--   $$\alpha\succsim_S\beta\iff\int_S u\circ\alpha\,d\rho\ \ge\ \int_S u\circ\beta\,d\rho .$$
--   4. The Lebesgue–Stieltjes measure of $\rho$ agrees with $\mu$ on every time span.
--
--   This is the passage from Theorem B.1(b) to Theorem 1 "$\Rightarrow$". The paper obtains it through the Horn–Tarski extension and a liminal density structure; on $[0,T]$ one may take $\rho(t)=\mu[\lfloor 0,t\rceil]$.
--
--   **Formalization Note.** $\rho$ is a Mathlib `StieltjesFunction`. Only its values on $[0,T]$ matter, and it is required to be continuous on all of $\mathbb R$.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, Math. Oper. Res. 46(3) (2021) 1203-1229; SSRN 3232014; HAL hal-03637876 (https://hal.science/hal-03637876v1), Appendix C, proof of Theorem 1, direction "⟹" (Claims 1–2 and eq. (C3)), with Lemma B.2(a) (eq. B11).

import Mathlib
import Definitions.Def_IntertempDUI_Finite_DUI
import Definitions.Def_IntertempDUI_Finite_Content

namespace IntertempDUI.Finite

/-- Proof of Theorem 1 "⟹" (p. 25) with Lemma B.2(a) (pp. 23–24): a content-utility
representation (u, μ) with μ nonatomic and of full support yields a continuous, strictly
increasing ρ with ρ(0) = 0, ρ(T) = 1, whose Lebesgue–Stieltjes measure agrees with μ on time
spans and which gives a DUI representation (8) together with u. -/
theorem lemma_B2_content_to_dui {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (u : X → ℝ) (μ : Set (Time T) → ℝ)
    (hrep : IsContentUtilityRep A pref u μ) (hfs : FullSupport μ) (hna : Nonatomic μ) :
    ∃ ρ : StieltjesFunction ℝ, IsDUIRep (le_of_lt hT) A pref ρ u ∧
      ∀ S, IsTimeSpan S → (ρ.measure (Subtype.val '' S)).toReal = μ S := by sorry

end IntertempDUI.Finite
