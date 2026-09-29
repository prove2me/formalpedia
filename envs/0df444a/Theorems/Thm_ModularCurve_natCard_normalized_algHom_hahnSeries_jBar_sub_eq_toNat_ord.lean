-- Prove2me | Theorems.Thm_ModularCurve_natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord
-- name    : ModularCurve.natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/8587e1e1-f8b9-5fed-a3fd-a5ba9f328005
-- title:
--   Normalised Hahn-series embeddings inducing a place above j₀
-- statement:
--   Let $N$ be a nonzero natural number and $j_0$ an element of $\overline{\mathbb{Q}}$. Write $F_N = \mathtt{modularFunctionFieldBar } N$ for the subfield of $\operatorname{LaurentSeries}(\overline{\mathbb{Q}})$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the field $\mathbb{Q}(\mathtt{divisorExpansions } N) \subseteq \operatorname{LaurentSeries}(\mathbb{Q})$, and let $\bar j = \mathtt{jBar } N \in F_N$ be the image of the $q$-expansion $j(q)$. A place of $F_N$ over $\overline{\mathbb{Q}}$ is a valuation subring containing $\overline{\mathbb{Q}}$, different from $F_N$ and a principal ideal ring, with $v.\mathtt{ord}$ the associated normalised integer valuation. Assume: $F_N$ is finite dimensional over $\overline{\mathbb{Q}}(\bar j)$; $S$ is a finite set of places consisting exactly of those $v$ with $v.\mathtt{ord}(\bar j - j_0) > 0$; the orders $v.\mathtt{ord}(\bar j - j_0)$ for $v \in S$ sum to $[F_N : \overline{\mathbb{Q}}(\bar j)]$; and every place $w$ with $e_w := w.\mathtt{ord}(\bar j - j_0) > 0$ is realised by a $\overline{\mathbb{Q}}$-algebra map $\varphi' : F_N \to \operatorname{LaurentSeries}(\overline{\mathbb{Q}})$ sending $\bar j - j_0$ to the monomial $t^{e_w}$ and satisfying $\operatorname{order}(\varphi' x) = w.\mathtt{ord}(x)$ for all $x$. Conclusion: for each such $w$, the number of $\overline{\mathbb{Q}}$-algebra maps $\psi$ from $F_N$ to the Hahn series over $\overline{\mathbb{Q}}$ with exponents in $\mathbb{Q}$ with $\psi(\bar j) = j_0 + t$ and such that for some rational $g > 0$ one has $\operatorname{order}(\psi x) = g \cdot w.\mathtt{ord}(x)$ for all $x$, equals $e_w$.
--
--   This counts, place by place, the normalised fractional-exponent expansions of the modular function field lying over a given value $j_0$ of the $j$-line, the ramification index at a place being exactly the order of vanishing of $\bar j - j_0$ there. It is an input to [`ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord`](thm.html#ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord) in the analysis of the fibres of the map to the $j$-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_MazurStepThreeInputs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve Polynomial

theorem ModularCurve.natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N)]
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀))
    (hsum : ∑ v ∈ S, v.ord (jBar N -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
      Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jBar N} : Set ↥(modularFunctionFieldBar N)))
        ↥(modularFunctionFieldBar N))

    (hP1 : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      ∃ φ' : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ]
          LaurentSeries (AlgebraicClosure ℚ),
        φ' (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
          HahnSeries.single (((w.ord (jBar N - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar N) j₀)).toNat : ℤ)) 1 ∧
        ∀ x, (φ' x).order = w.ord x)

    :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      Nat.card {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
        ∃ g : ℚ, 0 < g ∧ ∀ x, (w.ord x : ℚ) * g = (ψ x).order} =
      (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat := by sorry
