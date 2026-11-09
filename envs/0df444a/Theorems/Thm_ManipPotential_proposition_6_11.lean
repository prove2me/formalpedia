-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_11
-- name    : ManipPotential.proposition_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:55:29.161201+00:00
-- url     : https://prove2.me/theorems/1e0eaf79-0a6d-4d40-9696-2a0ff5dafc4f
-- title:
--   Proposition 6.11 — a unique Lipschitz family of common junctions
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, and let $g$ satisfy the axioms of Lemma 6.2. There is a nonempty open box $U \subset \mathbb R^{m! - m + 1}$ and a Lipschitz map
--   $$
--   G : U \to \Omega, \qquad G(y, \tau) = (H(y, \tau), y), \qquad \sum_{j=1}^m H_j(y, \tau) = \tau,
--   $$
--   such that:
--
--   1. for every $(y, \tau) \in U$, $G(y, \tau)$ is the **unique** common junction $(x, y)$ with external coordinates $y$ and $\sum_j x_j = \tau$;
--   2. every coordinate of $G(y, \tau)$ exceeds $1$;
--   3. at each point $z \in U$ where $G$ is differentiable, its Jacobian $J_G(z)$ has rank $m! - m + 1$.
--
--   Here $y$ ranges over the external coordinates ($m! - m$ of them) and $\tau$ is the total cyclic weight.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - generalization: λ > 1, a standing assumption from the remark after Lemma 6.6 (p.30, "for the rest of the proof, we can assume λ > 1") → no λ > 1 hypothesis: every K ∈ ℕ, so λ = K + 1 ≥ 1; reason: at K = 0 no g satisfies the axioms (remark after Lemma 6.6, item lambda_one_impossible), so the extra instances are vacuous and the statement specializes to the source
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: ℝ^{m!−m+1}, an open box, G : U → Ω, the rank of J_G(z) → (ExtRanking m → ℝ) × ℝ with its sup norm, a product of nonempty open intervals, a total map constrained on U, and the dimension of the range of fderiv at z; reason: Lipschitz continuity does not depend on the norm; G z ∈ Ω follows from the coordinate bound; same statement
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.11, p.33

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal

namespace ManipPotential

/-- Proposition 6.11 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.11, p.33): there is a nonempty open box
`U ⊂ ℝ^{m!−m+1}` and a Lipschitz map `G : U → Ω`, `G(y, τ) = (H(y, τ), y)` with `∑_j H_j(y, τ) = τ`,
such that for every `(y, τ) ∈ U`, `G(y, τ)` is the unique common junction `(x, y)` with
`∑_j x_j = τ`; every coordinate of `G(y, τ)` exceeds `1`; and at each `z ∈ U` where `G` is
differentiable, its Jacobian has rank `m! − m + 1`.

**Formalization Note** `ℝ^{m!−m+1}` is `(ExtRanking m → ℝ) × ℝ` (external coordinates `y`, then
`τ`); `G` is total and constrained on `U`; Lipschitz for the product sup norm. -/
theorem proposition_6_11 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    ∃ (a b : ExtRanking m → ℝ) (a₀ b₀ : ℝ) (U : Set ((ExtRanking m → ℝ) × ℝ)) (L : NNReal)
      (G : (ExtRanking m → ℝ) × ℝ → (Ranking m → ℝ)),
      (∀ s, a s < b s) ∧ a₀ < b₀ ∧
      U = (Set.univ.pi fun s => Set.Ioo (a s) (b s)) ×ˢ Set.Ioo a₀ b₀ ∧
      LipschitzOnWith L G U ∧
      (∀ z ∈ U, (∀ s : ExtRanking m, G z s.1 = z.1 s) ∧ cycTotal (G z) = z.2) ∧
      (∀ z ∈ U, IsCommonJunction g (G z)) ∧
      (∀ z ∈ U, ∀ P : Ranking m → ℝ, IsCommonJunction g P →
        (∀ s : ExtRanking m, P s.1 = z.1 s) → cycTotal P = z.2 → P = G z) ∧
      (∀ z ∈ U, ∀ r, 1 < G z r) ∧
      (∀ z ∈ U, DifferentiableAt ℝ G z →
        Module.finrank ℝ (LinearMap.range (fderiv ℝ G z).toLinearMap) = m.factorial - m + 1) := by sorry

end ManipPotential
