-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_10
-- name    : ManipPotential.lemma_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:54:53.676203+00:00
-- url     : https://prove2.me/theorems/2a446963-3f2b-4f2e-9ead-72c7c040e2d8
-- title:
--   Lemma 6.10 — support of perturbed common junctions
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, $\kappa = 2\, m!\, \lambda^m$, and let $g$ satisfy the axioms of Lemma 6.2. Let $P$ be a common junction and $0 < \varepsilon < \tfrac12 \min_{r \in \mathcal L(C)} P_r$. Let $v \in \mathbb R^m_{\ge 0}$ be a (possibly irrational) vector of cyclic coordinates whose support $S = \{j : v_j > 0\}$ is nonempty and proper, $\emptyset \ne S \subsetneq [m]$, with $\|v\|_1 > \kappa\varepsilon$. Then every rational profile $Q$ with
--   $$
--   \big\| Q - (P - \varepsilon \mathbf 1 + vL) \big\|_\infty < \frac{\varepsilon}{4} \qquad (13)
--   $$
--   has $g(Q) \in \{c_j : j \in S\}$. Here $vL = \sum_j v_j \ell_j$ and $\mathbf 1 \in \mathbb R^{m!}$ is the all-ones vector.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - generalization: λ > 1, a standing assumption from the remark after Lemma 6.6 (p.30, "for the rest of the proof, we can assume λ > 1") → no λ > 1 hypothesis: every K ∈ ℕ, so λ = K + 1 ≥ 1; reason: at K = 0 no g satisfies the axioms (remark after Lemma 6.6, item lambda_one_impossible), so the extra instances are vacuous and the statement specializes to the source
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: ‖·‖_∞, ε𝟙 and min_r P_r → Lean's sup norm on Ranking m → ℝ, the constant function ε, and Finset.inf' over all rankings; reason: same quantities
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.10, Eq. (13), p.32

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_supp
import Definitions.Def_ManipPotential_kappa

namespace ManipPotential

/-- Lemma 6.10 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.10, Eq. (13), p.32): let `κ = 2 m! λ^m`, `P` a common junction and
`0 < ε < ½ min_r P_r`. If `v ∈ ℝ^m_{≥0}` has nonempty proper support `S` and `‖v‖₁ > κε`, then every
rational profile `Q` with `‖Q − (P − ε𝟙 + vL)‖_∞ < ε/4` has `g(Q) ∈ {c_j : j ∈ S}`.

**Formalization Note** The norm on `Ranking m → ℝ` is Lean's sup norm, i.e. `‖·‖_∞`. -/
theorem lemma_6_10 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (P : Ranking m → ℝ) (hP : IsCommonJunction g P) (ε : ℝ) (hε : 0 < ε)
    (hεP : ε < (1 / 2) * Finset.univ.inf' Finset.univ_nonempty P)
    (v : Fin m → ℝ) (hv : 0 ≤ v) (hS : (supp v).Nonempty) (hS' : supp v ≠ Finset.univ)
    (hvκ : kappa m K * ε < ∑ j, v j) (Q : Ranking m → ℚ)
    (hQ : ‖(fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL v)‖ < ε / 4) :
    g Q ∈ supp v := by sorry

end ManipPotential
