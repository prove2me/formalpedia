-- Prove2me | Theorems.Thm_ModularCurve_finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore
-- name    : ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/509bc9a4-053d-5306-abc5-b4e3f4783c60
-- title:
--   Finiteness of H¹_{fppf}(Specℤ,mathcal J_m) for primary-torsion cores
-- statement:
--   Let $p$ and $q$ be primes, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, i.e. $p$ lies in the nonunits of $A$, and let $C$ be a term of the structure `JZeroNeronPrimaryTorsionCore p q A hA`. Such a $C$ consists of: a family $\mathcal J_m = C.\mathcal J\,m$ of abelian sheaves on the small fppf site of $\operatorname{Spec}\mathbb Z$ (`specInt`), together with commutative rings $H_m$ carrying $\mathbb Z$-Hopf algebra structures that are of finite type and flat over $\mathbb Z$; the hypothesis `ff_finite`, that $H_m\otimes_{\mathbb Z}\mathbb Z_{(\ell)}$ is a finite module over the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ for every prime $\ell\neq p$; isomorphisms `sectionsEquiv` between the sections of $\mathcal J_m$ over an fppf object $U$ and the additive group attached to the convolution monoid of $\mathbb Z$-algebra maps $H_m\to\Gamma(U.\mathrm{left},\top)$, natural in $U$ (`sectionsNat`); bijections `genericPoints` of the convolution monoid of maps $H_m\to\overline{\mathbb Q}$ with the subgroup of $J_0(p)$-points (`JZero p`, the degree-zero Picard group of the modular function field over $\overline{\mathbb Q}$) killed by $q^m$ and annihilated by some power of the Eisenstein maximal ideal, turning convolution into addition and commuting with the Galois action; and, summarised here, sheaves $Q_m$ with short exact sequences $0\to\mathcal J_m\to\mathcal J_{m+1}\to Q_m\to 0$, the analogous description of the $A$-points by the toric part of that subgroup, and Kummer-row data. The conclusion is that for every $m$ the group `fppfCohomology specInt (C.𝒥 m) 1`, i.e. $H^1$ of $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$, is finite.
--
--   This is the finiteness statement for the first fppf cohomology of the Eisenstein-primary torsion sheaves of the Néron model of $J_0(p)$, in the form needed when these sheaves are only quasi-finite flat at $p$. It is the input to [`ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow), which refines it to a statement on the order of the group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore (p : ℕ) [Fact p.Prime]
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) :
    ∀ m : ℕ, Finite (fppfCohomology specInt (C.𝒥 m) 1) := by sorry
