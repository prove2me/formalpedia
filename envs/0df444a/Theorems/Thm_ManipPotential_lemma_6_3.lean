-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_3
-- name    : ManipPotential.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:53:10.528369+00:00
-- url     : https://prove2.me/theorems/347202b8-672a-42f9-9656-0084dfd31553
-- title:
--   Lemma 6.3 — support of $g$ on sufficiently cyclic profiles
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, and let $g$ satisfy the axioms of Lemma 6.2. Suppose a rational profile $P \ge 0$ and a rational $u_0 \ge 0$ satisfy $g(P + u\,\ell_j) = c_j$ for every $j \in [m]$ and every rational $u > u_0$. Then for every nonzero $x \in \mathbb Q^m_{\ge 0}$ with $S = \mathrm{supp}(x)$,
--   $$
--   \|x\|_1 > \lambda^{|S| - 1} u_0 \ \Longrightarrow\ g(P + xL) \in \{c_j : j \in S\}.
--   $$
--   The same assertion holds with $r_j$ and $R$ in place of $\ell_j$ and $L$ throughout (both in the hypothesis and in the conclusion).
--
--   The lemma controls which candidates can win on profiles with a large cyclic component.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: candidates c_1…c_m, indices mod m, ℓ_j and r_j as printed → Fin m (0-based), ℓ_j : c ↦ j − c and r_j : c ↦ c − j as permutations to positions; reason: Lean convention; same rankings
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.3, p.27

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_cycR
import Definitions.Def_ManipPotential_supp

namespace ManipPotential

/-- Lemma 6.3 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.3, p.27): if a rational profile `P ≥ 0` and a rational `u₀ ≥ 0`
satisfy `g(P + u ℓ_j) = c_j` for every `j` and every rational `u > u₀`, then for every nonzero
`x ∈ ℚ^m_{≥0}` with `S = supp(x)`, `‖x‖₁ > λ^{|S|−1} u₀ ⟹ g(P + xL) ∈ {c_j : j ∈ S}`; and the same
with `r_j` and `R` in place of `ℓ_j` and `L` throughout. Here `λ = K + 1`. -/
theorem lemma_6_3 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (P : Ranking m → ℚ) (hP : 0 ≤ P) (u₀ : ℚ) (hu₀ : 0 ≤ u₀) :
    ((∀ (j : Fin m) (u : ℚ), u₀ < u → g (P + u • unitVec (ell j)) = j) →
      ∀ x : Fin m → ℚ, 0 ≤ x → x ≠ 0 →
        ((K : ℚ) + 1) ^ ((supp x).card - 1) * u₀ < ∑ j, x j → g (P + cycL x) ∈ supp x) ∧
    ((∀ (j : Fin m) (u : ℚ), u₀ < u → g (P + u • unitVec (rr j)) = j) →
      ∀ x : Fin m → ℚ, 0 ≤ x → x ≠ 0 →
        ((K : ℚ) + 1) ^ ((supp x).card - 1) * u₀ < ∑ j, x j → g (P + cycR x) ∈ supp x) := by sorry

end ManipPotential
