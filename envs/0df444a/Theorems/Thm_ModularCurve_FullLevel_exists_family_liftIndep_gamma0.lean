-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_family_liftIndep_gamma0
-- name    : ModularCurve.FullLevel.exists_family_liftIndep_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/4ffa6d85-2684-5305-9ca2-acc6f3e1b80e
-- title:
--   Integral functions independent over the level-M' field
-- statement:
--   Fix a prime $q$ with $q\ge 5$, a nonzero $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ lying in the nonunits of $A$. Let $F=$ `fieldBar q M'` be the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the level-$(q^2M',H)$ function field over $\mathbb{Q}$, where $H=$ `levelH q M'` is the kernel of the reduction map of units attached to `dvd_sq_mul q M'`, and let $R$ be a regular prolongation of $A$ to $F$ with residue field target the field $\mathrm{qExpFunctionFieldC}(\kappa_A,\Gamma_H(q^2M'))$ generated over the residue field $\kappa_A$ of $A$ by ratios of integral $q$-expansions of equal-weight modular forms on $\Gamma_H(q^2M')$; thus $R$ consists of a valuation subring $\mathcal{O}=R.\mathrm{integers}$ of $F$ and a surjective residue homomorphism with kernel the maximal ideal, compatible with $A$ and its residue map, and with the usual scaling property. It is assumed in addition that $\mathcal{O}$ is exactly the set of $f\in F$ admitting $x,y\in A((q))$ with the coefficientwise reduction of $y$ nonzero and $f\cdot y=x$ in $\overline{\mathbb{Q}}((q))$, and that every $y\in A((q))$ whose image lies in $F$ lies in $\mathcal{O}$ with residue the coefficientwise reduction of $y$. The conclusion: there are $a\in\mathbb{N}$ and $u_1,\dots,u_a\in F$, all in $\mathcal{O}$, with $q-1<4a$, such that for every $d_1,\dots,d_a\in F$ lying in $\mathcal{O}$ and, as Laurent series, in the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of $\mathrm{qExpFunctionFieldC}(\mathbb{Q},\Gamma_0(M'))$, the inequality $v(\sum_i d_iu_i)<1$ for the valuation of $\mathcal{O}$ forces $v(d_i)<1$ for every $i$.
--
--   This is the quantitative half of Igusa irreducibility in lift form: the residues of the $u_i$ are linearly independent over the residue field of the level-$M'$ Gauss ring, and more than a quarter of the full Igusa degree $(q-1)/2$ suffices. It feeds the counting argument for Borel stability of the Gauss ring, via [`ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq`](thm.html#ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq), and relies on the existence of a Gauss-integral function whose residue is the Eisenstein ratio $E_4E_6/\Delta$ together with the vanishing criterion for such Eisenstein-ratio powers over the level-$M'$ function field in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_family_liftIndep_gamma0.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_family_liftIndep_gamma0
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (R : RegularProlongation A (fieldBar q M')
      (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))
    (hq : 5 ≤ q) (hqM' : ¬ q ∣ M') (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    ∃ (a : ℕ) (u : Fin a → fieldBar q M'), (∀ i, u i ∈ R.integers) ∧ q - 1 < 4 * a ∧
      ∀ d : Fin a → fieldBar q M', (∀ i, d i ∈ R.integers ∧
        (d i : LaurentSeries (AlgebraicClosure ℚ)) ∈
          laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) →
        R.integers.valuation (∑ i, d i * u i) < 1 → ∀ i, R.integers.valuation (d i) < 1 := by sorry
