-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_lemma_B_1_upper_image_monotone
-- name    : MeanRiskBellman.Recursion.lemma_B_1_upper_image_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:37.691758+00:00
-- url     : https://prove2.me/theorems/d6422d09-3467-4e05-8e76-7c51dc29018f
-- title:
--   Lemma B.1, last sentence, p. 29 — the upper image is monotone: p ∈ P_t(v_t), p ≤ q ⇒ q ∈ P_t(v_t)
-- statement:
--   In the mean-risk market under Assumption 2.2, let $0\le t\le T$ and $v_t\in L_t$. The upper image $\mathcal P_t(v_t)$ (with $\mathcal P_T(v_T)=\{(-v_T,-v_T)\}+L_T(\mathbb R^2_+)$ by (5.2)) has the monotonicity property of upper images with respect to the convex ordering cone $L_t(\mathbb R^2_+)$: if $p\in\mathcal P_t(v_t)$ and $q\in L_t(\mathbb R^2)$ with $p\le q$, i.e. $q-p\in L_t(\mathbb R^2_+)$, then
--   $$q\in\mathcal P_t(v_t).$$
--
--   The paper states this for the upper image of any vector optimization problem with a convex ordering cone; this item is its instance for the upper images of the mean-risk problems, the form in which the proofs of Lemma 5.2 and Theorem 5.1 use it.
--
--   **Formalization Note.** The order is pointwise and componentwise; $q$ is required to be $\mathcal F_t$-measurable, which together with $p\le q$ is $p\le_{L_t(\mathbb R^2_+)}q$ (elements of $\mathcal P_t(v_t)$ are $\mathcal F_t$-measurable).
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 29, Lemma B.1, last sentence (instance for P_t(v_t), with (5.2) p. 13)

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

namespace MeanRiskBellman.Recursion

theorem lemma_B_1_upper_image_monotone {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (M : Market Ω) (hM : M.Assumptions) (t : ℕ) (ht : t ≤ M.T) (v : Ω → ℝ)
    (hv : StronglyMeasurable[M.ℱ t] v) (p q : Ω → ℝ × ℝ) (hp : p ∈ upperImage M t v)
    (hq : StronglyMeasurable[M.ℱ t] q) (hpq : p ≤ q) :
    q ∈ upperImage M t v := by sorry

end MeanRiskBellman.Recursion
