-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_B2_dui_to_content
-- name    : IntertempDUI.Finite.lemma_B2_dui_to_content
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T16:14:58.62797+00:00
-- url     : https://prove2.me/theorems/7c79bbaf-25bb-46a2-946e-d9b756e3b767
-- title:
--   DUI representation ⟹ nonatomic full-support content-utility representation
-- statement:
--   Let $T>0$ and let $\mathcal X$ be connected. Let $\mathcal A\subseteq C([0,T],\mathcal X)$ contain the constant trajectories. Let $\{\succsim_I\}$ be an intertemporal preference structure satisfying the standing assumptions (each $\succsim_I$ is complete, transitive, nontrivial and depends only on restrictions to $I$). Assume $\mathcal A$ satisfies (MinEqn), which the paper calls (LV).
--
--   Suppose $(\rho,u)$ is a discounted utility integral representation (8). That is, $u$ is continuous, $\rho$ is continuous with $\rho(0)=0$ and $\rho(T)=1$, $\rho$ is strictly increasing on $[0,T]$, and for every time span $S$ (and every time interval $I$)
--   $$\alpha\succsim_S\beta\iff \int_S u\circ\alpha\,d\rho\ \ge\ \int_S u\circ\beta\,d\rho .$$
--   Let $\nu_\rho$ be the Lebesgue–Stieltjes measure of $\rho$, and define $\mu[S]:=\nu_\rho[S]$ for time spans $S$. Then:
--
--   1. $(u,\mu)$ is a content-utility representation (B6), with the intermittent orders $\succsim_S$ given by $\mathfrak I^\mu_S[u\circ\alpha]\ge\mathfrak I^\mu_S[u\circ\beta]$;
--   2. $\mu$ has full support;
--   3. $\mu$ is nonatomic.
--
--   Point 1 includes four facts: $\mu$ is a normalized finitely additive content on time spans, $u$ represents $\succsim_{sy}$, each $u\circ\alpha$ is comeasurable, and the content integral $\mathfrak I^\mu_S$ agrees with the Stieltjes integral on these trajectories.
--
--   This is the bridge from the representation (8) to the content-utility representation of Theorem B.1. It gives the "$\Leftarrow$" direction of Theorem 1 and the reduction of its uniqueness clause to that of Theorem B.1.
--
--   **Formalization Note.** The content is $S\mapsto\nu_\rho(S)$, written in Lean as `(ρ.measure (Subtype.val '' S)).toReal`.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, Math. Oper. Res. 46(3) (2021) 1203-1229; SSRN 3232014; HAL hal-03637876 (https://hal.science/hal-03637876v1), Appendix B, Lemma B.2(a1),(b) (eqs. B11, B12) together with Lemma B.1, as used in Appendix C, proof of Theorem 1, direction "⇐".

import Mathlib
import Definitions.Def_IntertempDUI_Finite_DUI
import Definitions.Def_IntertempDUI_Finite_Content

namespace IntertempDUI.Finite

/-- Lemma B.2(a1),(b) (pp. 23–24) with Lemma B.1, as used in the proof of Theorem 1 "⇐" (p. 25):
a DUI representation (ρ,u) yields the content-utility representation (u, μ) with
μ[S] = ν_ρ[S], a nonatomic content with full support. -/
theorem lemma_B2_dui_to_content {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref) (hM : MinEqn A pref)
    (ρ : StieltjesFunction ℝ) (u : X → ℝ)
    (hrep : IsDUIRep (le_of_lt hT) A pref ρ u) :
    IsContentUtilityRep A pref u (fun S => (ρ.measure (Subtype.val '' S)).toReal) ∧
      FullSupport (fun S : Set (Time T) => (ρ.measure (Subtype.val '' S)).toReal) ∧
      Nonatomic (fun S : Set (Time T) => (ρ.measure (Subtype.val '' S)).toReal) := by sorry

end IntertempDUI.Finite
