-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_isGoodDivisor_add_of_ord_residue_eq_neg
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isGoodDivisor_add_of_ord_residue_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/bbce0cf6-1ff8-53f6-a53d-3d8487fb48a2
-- title:
--   Exact branch orders make E+divG effective and good
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}:A\to k$; fix modular polynomial data `data` for $q$ together with the Kronecker congruence `hKr`, asserting that the reduction of $\Phi$ modulo $q$ equals $(Y^q-X)(Y-X^q)$, and the hypotheses `hα`, `hβ` that the two degeneracy maps $\overline{\mathbb Q}(X_0(1))\to\overline{\mathbb Q}(X_0(q))$ (`heckeAlphaBar`, `heckeBetaBar`, with $N=1$, $\ell=q$) are integral. Let $P$ be a `PlaceSpecialization` for these data, with its two reduction maps $\mathrm{red}_1=P.\mathtt{redFst}$, $\mathrm{red}_2=P.\mathtt{redSnd}$ from places of `modularFunctionFieldBar (1 * q)` to places of `modularFunctionFieldC k 1`, and write $\varphi$ for `frobOnPlacesGeomLevel k 1 data hKr`. Let $R$ be a level-one prolongation pair for $P$: a coefficient map $\overline{\mathrm{red}}$ on the residue field of $A$ lifting $\mathrm{red}$, an induced embedding $\iota$ of modular function fields, and two regular prolongations $R_1,R_2$ of $A$ to $\overline{\mathbb Q}(X_0(q))$ with residue field `modularFunctionFieldFullC (ResidueField A) 1`, $R_2$ being the Fricke conjugate of $R_1$. Assume $R.\mathtt{IsModel}$, i.e. the divisor laws computing, for any $f$ integral for both prolongations with nonzero residues and any divisor $D$ with $D(W)=\operatorname{ord}_W f$, the push-forward under $\mathrm{red}_1$ (resp. $\mathrm{red}_2$) of the strict type-one (resp. type-two) part of $D$ at places $v$ with $\varphi^2v\neq v$ as $\operatorname{ord}_v$ of the first (resp. second) residue of $f$, together with the two cusp laws at $\mathrm{red}_1(\infty)$ and $\mathrm{red}_2(0)$; and assume $R.\mathtt{OrderLawFixed}$, i.e. for such $f$ and $D$ and every $v$ with $\varphi^2v=v$, $v\neq\mathrm{red}_1(\infty)$, one has $(\mathrm{red}_{1*}D)(v)=\operatorname{ord}_v(\mathrm{res}_1f)+\operatorname{ord}_{\varphi v}(\mathrm{res}_2f)$. Let $S_0\subset k$ be a finite set whose elements are exactly the members of `ssJSet q k` (those $j$ such that every elliptic curve over $k$ with $j$-invariant $j$ has no nonzero affine point killed by $q$), let $E$ be a divisor of $\overline{\mathbb Q}(X_0(q))$, $D_1,D_2$ divisors of `modularFunctionFieldC k 1`, $\lambda:k\to k$, and assume $R.\mathtt{SplitDatum}\,S_0\,E\,D_1\,D_2\,\lambda$ (interlacing bounds for $D_1$, $D_2(\varphi v)$ between the negative and positive parts of $\mathrm{red}_{1*}E$ at $\varphi^2$-fixed non-cuspidal $v$, additivity of degrees, non-vanishing of $\lambda$ on $S_0$, agreement of $D_1,D_2$ with the push-forwards of the type-one and type-two parts of $E$ off the $\varphi^2$-fixed places, the summation law $D_1(v)+D_2(\varphi v)=(\mathrm{red}_{1*}E)(v)$ at $\varphi^2$-fixed non-cuspidal $v$, the prescribed cusp values, and a transfer of Riemann–Roch spaces along the residues with node data; summarised here). Let $G$ be an element of `modularFunctionFieldBar (1 * q)` lying in $R_1.\mathtt{integers}$ and $R_2.\mathtt{integers}$ with both residues nonzero and with $G$ in the Riemann–Roch space of $E$, let $D_G$ be the divisor $W\mapsto\operatorname{ord}_W G$, and let $\Delta_1,\Delta_2$ be the divisors $v\mapsto\operatorname{ord}_v(R.\mathtt{residue₁}\,G)$ and $v\mapsto\operatorname{ord}_v(R.\mathtt{residue₂}\,G)$. Assume the branch orders are exact: for every place $v$ with $\varphi^2v=v$ and $v\neq\mathrm{red}_1(\mathtt{cuspInftyBar})$ one has $\operatorname{ord}_v(R.\mathtt{residue₁}\,G)+D_1(v)=0$ and $\operatorname{ord}_{\varphi v}(R.\mathtt{residue₂}\,G)+D_2(\varphi v)=0$, and the analogous vanishing holds at $\mathrm{red}_1(\mathtt{cuspInftyBar})$ for $(\mathrm{residue}_1,D_1)$ and at $\mathrm{red}_2(\mathtt{cuspZeroBar})$ for $(\mathrm{residue}_2,D_2)$. Then $E+D_G$ is effective, it is a good divisor for $P$ (every place in its support is of strict type one, $\varphi(\mathrm{red}_1W)=\mathrm{red}_2W$ with $\varphi^2(\mathrm{red}_1W)\neq\mathrm{red}_1W$, or of strict type two, $\mathrm{red}_1W=\varphi(\mathrm{red}_2W)$ with $\varphi^2(\mathrm{red}_2W)\neq\mathrm{red}_2W$), and the push-forward under $\mathrm{red}_1$ of the type-one part of $E+D_G$ equals $D_1+\Delta_1$, while the push-forward under $\mathrm{red}_2$ of its type-two part equals $D_2+\Delta_2$.
--
--   This is a bookkeeping step in the specialization of divisor classes on $X_0(q)$ at the prime $q$, where the special fibre consists of two rational components meeting at the supersingular points: a function $G$ in $L(E)$ that is integral for both prolongations of the $q$-adic place and whose residues have exactly the pole orders prescribed by the split datum at the $\varphi^2$-fixed places and at the two cusps converts $E$ into the effective good divisor $E+\operatorname{div}G$ with controlled push-forwards. It is used by the two lemmas producing good admissible representatives of classes of the form $\lambda\cdot\delta_a-\delta$ on the glued Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_isGoodDivisor_add_of_ord_residue_eq_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplit
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isGoodDivisor_add_of_ord_residue_eq_neg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k ↥(modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (G : ↥(modularFunctionFieldBar (1 * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hG₁ : R.R₁.residue ⟨G, h₁⟩ ≠ 0) (hG₂ : R.R₂.residue ⟨G, h₂⟩ ≠ 0)
    (hGE : G ∈ riemannRochSpace E)
    (DG : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDG : ∀ W, DG W = W.ord G)
    (Δ₁ Δ₂ : Divisor k ↥(modularFunctionFieldC k 1))
    (hΔ₁ : ∀ v, Δ₁ v = v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k 1)))
    (hΔ₂ : ∀ v, Δ₂ v = v.ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k 1)))
    (hfix : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k 1)) + D₁ v = 0 ∧
      (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k 1)) +
        D₂ (frobOnPlacesGeomLevel k 1 data hKr v) = 0)
    (hcusp₁ : (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k 1)) +
      D₁ (P.redFst (cuspInftyBar (1 * q))) = 0)
    (hcusp₂ : (P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k 1)) +
      D₂ (P.redSnd (cuspZeroBar (1 * q))) = 0) :
    (∀ W, 0 ≤ (E + DG) W) ∧ P.IsGoodDivisor (E + DG) ∧
      Finsupp.mapDomain P.redFst (P.fstPart (E + DG)) = D₁ + Δ₁ ∧
      Finsupp.mapDomain P.redSnd (P.sndPart (E + DG)) = D₂ + Δ₂ := by sorry
