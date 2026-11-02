-- Prove2me | Theorems.Thm_IntertempDUI_Finite_theorem_B2_b_forward
-- name    : IntertempDUI.Finite.theorem_B2_b_forward
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T17:10:59.859866+00:00
-- url     : https://prove2.me/theorems/955c3aad-349a-4f3e-b2ba-f3ce6482a454
-- title:
--   Theorem B.1(b), ⟹: the eight axioms yield a nonatomic content-utility representation
-- statement:
--   Let $\mathcal T=[0,T]$ with $T>0$, and let $\mathcal X$ be a connected topological space. Let $\mathcal A\subseteq C([0,T],\mathcal X)$ contain all constant trajectories. Let $\{\succsim_I\}$ be an intertemporal preference structure satisfying the standing assumptions: each $\succsim_I$ is complete, transitive, nontrivial and depends only on restrictions to $I$. Assume the structural conditions (R\*) and (MinEqn), the latter being the paper's (LV).
--
--   If $\{\succsim_I\}$ satisfies the eight axioms
--   $$\text{(ISep), (LSep), (StEq), (C), (Dom), (CIP), (TC), (Eph)},$$
--   then it admits a content-utility representation (B6). That is, there are a continuous $u:\mathcal X\to\mathbb R$ and a normalized content $\mu$ on the Boolean algebra of time spans with three properties:
--
--   1. $u$ represents $\succsim_{sy}$ and each $u\circ\alpha$ is comeasurable;
--   2. for every time span $S$ (and every time interval),
--   $$\alpha\succsim_S\beta\iff\mathfrak I^\mu_S[u\circ\alpha]\ \ge\ \mathfrak I^\mu_S[u\circ\beta];$$
--   3. $\mu$ has full support and is nonatomic.
--
--   This is the sufficiency half of the content representation theorem, which the paper adapts from the subjective expected utility theorem of its companion paper. It is the deep step behind Theorem 1. The converse direction and the uniqueness clause of Theorem B.1(b) hold under the same hypotheses and are proved separately on the platform.
--
--   **Formalization Note.** The content integral $\mathfrak I^\mu_S$ is the supremum of lower sums over finite partitions of $S$ by time spans (definition `integrator`).
-- source:
--   Pivato, Intertemporal choice with continuity constraints, Math. Oper. Res. 46(3) (2021) 1203-1229; SSRN 3232014; HAL hal-03637876 (https://hal.science/hal-03637876v1), Appendix B, Theorem B.1(a) and (b), direction "⟹" (pp. 20-22 of the HAL version; pp. 27-28 of the SSRN version).

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Content

namespace IntertempDUI.Finite

/-- Theorem B.1(b), direction "⟹" (pp. 20–22), for [0,T]: the eight axioms yield a
content-utility representation with a nonatomic content of full support. -/
theorem theorem_B2_b_forward {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : RichnessStar A pref) (hM : MinEqn A pref) :
    (ISep A pref ∧ LSep A pref ∧ StEq A pref ∧ CondC pref ∧
      Dom A pref ∧ CIP A pref ∧ TC A pref ∧ Eph A pref) →
      ∃ u : X → ℝ, ∃ μ : Set (Time T) → ℝ,
        IsContentUtilityRep A pref u μ ∧ FullSupport μ ∧ Nonatomic μ := by sorry

end IntertempDUI.Finite
