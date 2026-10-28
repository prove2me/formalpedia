-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_cost_eq_max_box
-- name    : ModelFreeBounds.Duality.cost_eq_max_box
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:32.477723+00:00
-- url     : https://prove2.me/theorems/a9da1d7f-a82f-4e73-81f9-673326e6ed8e
-- title:
--   Appendix EC.4, display after (EC.4.1), pp. ec15–ec16 — π(y) = max over q ∈ Δ of ⟨y, q⟩
-- statement:
--   Let $\Omega$ be a Polish space and consider a market with Borel payoffs $g_1,\dots,g_m$ and bid–ask prices $\underline\pi_j\le\overline\pi_j$. Let $\Delta=[\underline\pi_1,\overline\pi_1]\times\cdots\times[\underline\pi_m,\overline\pi_m]$. Then for every $y\in\mathbb R^m$ the cost $\pi(y)=\sum_j y_j^+\overline\pi_j-y_j^-\underline\pi_j$ is the maximum of the linear function $q\mapsto\langle y,q\rangle$ over $\Delta$:
--   $$\pi(y)=\max_{q\in\Delta}\langle y,q\rangle .$$
--   That is, $\pi(y)=\langle y,q\rangle$ for some $q\in\Delta$, and $\langle y,q\rangle\le\pi(y)$ for every $q\in\Delta$.
--
--   This identity shows that $\pi$ is the support function of the box $\Delta$, hence sublinear; it is used in the weak-duality direction of Theorem 2.4(iii) and in Lemma EC.4.2.
--
--   **Formalization Note** The maximum is stated as `IsGreatest` of the image of $\Delta$ under $q\mapsto\sum_j y_jq_j$. The standing assumptions of §2 (Polish $\Omega$, Borel $g_j$, $\underline\pi_j\le\overline\pi_j$) are binders; only $\underline\pi_j\le\overline\pi_j$ matters here, and it makes $\Delta$ nonempty.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Appendix EC.4, display after (EC.4.1), pp. ec15–ec16

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem cost_eq_max_box {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (y : Fin m → ℝ) :
    IsGreatest ((fun q : Fin m → ℝ => ∑ j, y j * q j) '' M.box) (M.cost y) := by sorry

end ModelFreeBounds.Duality
