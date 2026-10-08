-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_lemma_11_b
-- name    : HuImkellerMuller.Exponential.lemma_11_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:59.630183+00:00
-- url     : https://prove2.me/theorems/2f2cc9fd-4d33-492c-a787-e5ed8056bf85
-- title:
--   Lemma 11 (b), p. 13 — there is a predictable a* with a*_t ∈ Π_{C_t}(a_t) for all t
-- statement:
--   Let $(a_t)$ be an $\mathbb R^{1\times m}$-valued and $(\sigma_t)$ an $\mathbb R^{d\times m}$-valued predictable process with $\sigma_t(\omega)$ of full rank $d$ for every $(t,\omega)$, let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed and nonempty, and $C_t=\tilde C\sigma_t$. Then there exists a predictable process $a^*$ with
--   $$a^*_t\in\Pi_{C_t}(a_t)\qquad\text{for all } t,\ \omega .$$
--
--   This is the measurable selection of nearest points used to build the optimal strategy (8) of Theorem 7: since $\tilde C$ need not be convex, $\Pi_{C_t}(a_t)$ may contain several points, and the lemma chooses one of them predictably.
--
--   **Formalization Note** Two hypotheses are added to the page's: $\tilde C\neq\emptyset$ (otherwise $\Pi$ is empty), and full rank of $\sigma_t(\omega)$ for every $(t,\omega)$. The lemma itself asks only that $\sigma$ be predictable, but the image of a closed set under a rank-deficient matrix need not be closed and $\Pi_{C_t}(a_t)$ can then be empty; §1 assumes full rank, and (4)'s remark that $C_t(\omega)$ is closed relies on it.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, Lemma 11 (b), pp. 12–13

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_Market

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- Lemma 11 (b), p. 13: for predictable a and σ (σ_t(ω) of full rank) and a nonempty closed C̃,
there is a predictable a* with a*_t ∈ Π_{C_t}(a_t) for all t. -/
theorem lemma_11_b {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}
    (𝓕 : Filtration ℝ≥0 mΩ)
    (a : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (ha : IsPredictable 𝓕 a) (hσ : ∀ i j, IsPredictable 𝓕 (fun t ω => σ t ω i j))
    (hrank : ∀ t ω, (σ t ω).rank = d)
    (Ct : Set (Fin d → ℝ)) (hCt : IsClosed Ct) (hne : Ct.Nonempty) :
    ∃ astar : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m), IsPredictable 𝓕 astar ∧
      ∀ t ω, astar t ω ∈ proj (Cset Ct σ t ω) (a t ω) := by sorry

end HuImkellerMuller.Exponential
