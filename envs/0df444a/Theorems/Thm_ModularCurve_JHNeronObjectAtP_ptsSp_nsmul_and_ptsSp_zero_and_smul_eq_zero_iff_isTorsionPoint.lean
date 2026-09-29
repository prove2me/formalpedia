-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/bfadbd4d-68c6-5a59-bc1a-3126ba8051fa
-- title:
--   Special-fibre dictionary respects multiples, identity and torsion
-- statement:
--   Fix natural numbers $p$ (prime) and $M$ (non-zero), a subgroup $H \le (\mathbb{Z}/M)^\times$ and a divisibility $p \mid M$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ lies in the non-units of $A$, whose residue field is of characteristic $p$ and algebraically closed. Let $\Lambda$ be a `LevelData` for $(p,M,H,A)$, that is, a morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` restricting to the generic point over $\overline{\mathbb{Q}}$, a scheme $X$ over `base p` with a relative group law, and parametrisations of the generic and special points; and let $O$ be a `JHNeronObjectAtP` over these data, with structural morphism $g$, relative group law $O.L$, finite set of glueing places $O.\mathrm{ssFinset}$, and special-fibre parametrisation $O.\mathrm{ptsSp}$, a bijection from $\mathrm{GluedPic}^0$ of the function field `Fbar` over the residue field of $A$ — the quotient of admissible glueing data (pairs of degree-zero divisors vanishing at the glued places, together with unit data) by the glued principal subgroup — onto the points over $\sigma_A$ composed after the residue morphism `resPt A`. The conclusion has three parts: for every $k \in \mathbb{N}$ and every glued class $z$, $O.\mathrm{ptsSp}(k \cdot z)$ equals the $k$-fold iterate $O.L.\mathrm{nsmul}$ (defined by $0 \mapsto$ the identity section and $n+1 \mapsto$ multiplication of the $n$-th iterate by the point) applied to $O.\mathrm{ptsSp}(z)$; $O.\mathrm{ptsSp}(0)$ is the identity section of $O.L$ over that point; and $k \cdot z = 0$ holds if and only if $O.\mathrm{ptsSp}(z)$ is $k$-torsion for $O.L$, i.e. its $k$-fold iterate equals the identity section.
--
--   This is the compatibility statement making the special-fibre parametrisation of the Néron object at a place above $p$ an isomorphism of $\mathbb{N}$-modules up to the relative group law, so that vanishing of $k \cdot z$ in the glued Picard group is the same as $k$-torsion of the corresponding point. It is used in the level-$\Gamma_H(M)$ analysis at $p$, for instance in the statements on $p^n$-torsion in the toric part and on the extension of glued classes to places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    (∀ (k : ℕ) (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      O.ptsSp (k • z) = O.L.nsmul (resPt A ≫ Λ.σA) k (O.ptsSp z)) ∧
    O.ptsSp 0 = O.L.one (resPt A ≫ Λ.σA) ∧
    (∀ (k : ℕ) (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      k • z = 0 ↔ O.L.IsTorsionPoint (resPt A ≫ Λ.σA) k (O.ptsSp z)) := by sorry
