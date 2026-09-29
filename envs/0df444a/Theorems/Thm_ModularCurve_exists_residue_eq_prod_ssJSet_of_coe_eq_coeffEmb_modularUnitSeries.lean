-- Prove2me | Theorems.Thm_ModularCurve_exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries
-- name    : ModularCurve.exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/e98a60f8-6154-55e8-9638-9da9e77cee6b
-- title:
--   Ogg's unit reduces to the supersingular polynomial in ̄ j
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $p$, an intermediate field $F$ of $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$, an intermediate field $\bar F$ of $\kappa((q))$ over $\kappa$, and a `RegularProlongation` $R$ of $A$ to $F$ with residue field $\bar F$: a valuation subring $R.\mathrm{integers} \subseteq F$ whose intersection with $\overline{\mathbb Q}$ is exactly $A$, together with a surjective ring homomorphism $R.\mathrm{residue} : R.\mathrm{integers} \to \bar F$ whose kernel is the maximal ideal, which on $A$ induces the residue map $A \to \kappa \to \bar F$, and such that every nonzero $f \in F$ admits $c \in \overline{\mathbb Q}$ with $c\cdot f \in R.\mathrm{integers}$ of nonzero residue. Assume further (hypothesis `hR`) that every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb Q}((q))$ lies in $F$ lies in $R.\mathrm{integers}$, with residue the coefficientwise reduction of $y$ in $\kappa((q))$. Let $G \in F$ have $q$-expansion the image in $\overline{\mathbb Q}((q))$ of `modularUnitSeries p`, namely $\Delta(q)/\Delta(q^p)$, where $\Delta(q) = q\prod_{n\ge 1}(1-q^n)^{24}$ and $\Delta(q^p)$ is its $q \mapsto q^p$ substitution. The conclusion asserts that both $G$ and $G^{-1}$ lie in $R.\mathrm{integers}$, and produces a finite set $S_0 \subseteq \kappa$ and exponents $n : \kappa \to \mathbb N$ such that: $S_0$ has exactly the elements of `ssJSet p` $\kappa$, i.e. those $j \in \kappa$ for which every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $j$ has no nonzero point killed by $p$; $n(a) > 0$ for $a \in S_0$; $\sum_{a \in S_0} n(a) = p - 1$ (truncated subtraction in $\mathbb N$); the image of $R.\mathrm{residue}(G)$ in $\kappa((q))$ equals $\prod_{a \in S_0}(\mathrm{jqModC}\,\kappa - a)^{n(a)}$, where $\mathrm{jqModC}\,\kappa = q^{-1}\,(E_4^3\eta^{-24})$ reduced coefficientwise to $\kappa$, the $q$-expansion of $j$; and, for any $\bar x \in \bar F$ whose image in $\kappa((q))$ is that $q$-expansion of $j$, the identity $R.\mathrm{residue}(G) = \prod_{a \in S_0}(\bar x - a)^{n(a)}$ holds in $\bar F$.
--
--   This is the statement, in the Gauss-valuation form at the cusp $\infty$, that Ogg's unit $\Delta(\tau)/\Delta(p\tau)$ restricted to the component of the special fibre containing $\infty$ is a unit of the local ring whose residue is the supersingular polynomial in $\bar j$, with positive multiplicities summing to $p-1$; only the prolongation at $\infty$ enters, so no level structure appears. It feeds the construction of a vertical unit on the Deligne–Rapoport model used in [`ModularCurve.XHDRModelAtP.exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries.lean

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p]
    (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (Fb : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
    (R : RegularProlongation A ↥F ↥Fb)

    (hR : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ F),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥F) ∈ R.integers,
        ((R.residue ⟨_, h⟩ : ↥Fb) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (G : ↥F) (hG : ((G : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p)) :
    ∃ (S₀ : Finset (ResidueField ↥A)) (n : ResidueField ↥A → ℕ) (hG₁ : G ∈ R.integers),

      G⁻¹ ∈ R.integers ∧

      (∀ a, a ∈ S₀ ↔ a ∈ @ssJSet p (ResidueField ↥A) _ (Classical.decEq _)) ∧ (∀ a ∈ S₀, 0 < n a) ∧
      (∑ a ∈ S₀, n a = p - 1) ∧

      ((R.residue ⟨G, hG₁⟩ : ↥Fb) : LaurentSeries (ResidueField ↥A)) =
        ∏ a ∈ S₀, (jqModC (ResidueField ↥A) - HahnSeries.C a) ^ n a ∧

      ∀ xb : ↥Fb, ((xb : ↥Fb) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
        R.residue ⟨G, hG₁⟩ = ∏ a ∈ S₀, (xb - algebraMap (ResidueField ↥A) ↥Fb a) ^ n a := by sorry
