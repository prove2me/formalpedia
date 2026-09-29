-- Prove2me | Theorems.Thm_ModularCurve_valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd
-- name    : ModularCurve.valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/3626ed87-5291-516e-8dc3-9c6025e29497
-- title:
--   Unique branch over the j-line for Γ₀(M') when q ∤ M'
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q \nmid M'$, and $L$ a field of characteristic zero. Let $K_0$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the image, under the coefficientwise map induced by $\mathbb{Q} \to L$, of the subfield of $\mathbb{Q}((T))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$ of integral $q$-expansions of modular forms $f,g$ of weight $k$ for $\Gamma_0(M')$ with nonzero denominator. Let $A$ be a discrete valuation ring which is an $L$-subalgebra with $L$ as fraction field, and suppose the image of $q$ lies in the maximal ideal of $A$. Let $j_0 \in K_0$ have underlying Laurent series the coefficientwise image of $\mathrm{jq} = \mathrm{single}(-1,1) \cdot \mathrm{ofPowerSeries}\,\mathrm{jNumQ}$. Let $V, V'$ be valuation subrings of $K_0$, each satisfying: the image of every element of $A$ (via $A \to L \to K_0$) lies in the subring; the image of every element of the maximal ideal of $A$ is a nonunit of it; and for every $P \in A[X]$ whose reduction modulo the maximal ideal is nonzero, the value of $P$ (with coefficients pushed to $L$) at $j_0$ and the inverse of that value both lie in the subring. Then $V = V'$.
--
--   This is the valuation-theoretic form of the good-reduction statement for $X_0(M')$ at a prime $q \nmid M'$ together with geometric irreducibility of the special fibre (Igusa; Deligne–Rapoport): the branch rings described, which are the local rings at the generic points of the special-fibre components dominating the $j$-line of the normalisation of the projective $j$-line over $A$ in $K_0$, are all equal, so there is a single such branch. It is used in the full-level analysis of integral models and of the reduction behaviour of modular functions, where the uniqueness pins down the valuation attached to a chosen branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (V V' : ValuationSubring ↥K₀)
    (hV : (∀ a : A, algebraMap L ↥K₀ (algebraMap A L a) ∈ V) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap L ↥K₀ (algebraMap A L a) ∈ V.nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j₀ (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j₀ (P.map (algebraMap A L)))⁻¹ ∈ V))
    (hV' : (∀ a : A, algebraMap L ↥K₀ (algebraMap A L a) ∈ V') ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap L ↥K₀ (algebraMap A L a) ∈ V'.nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j₀ (P.map (algebraMap A L)) ∈ V' ∧ (Polynomial.aeval j₀ (P.map (algebraMap A L)))⁻¹ ∈ V')) :
    V = V' := by sorry
