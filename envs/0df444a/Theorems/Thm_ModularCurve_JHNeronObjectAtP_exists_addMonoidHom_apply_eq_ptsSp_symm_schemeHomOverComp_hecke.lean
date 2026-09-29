-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
-- name    : ModularCurve.JHNeronObjectAtP.exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/7ba10f15-889a-5f47-a3db-bba155d47a6f
-- title:
--   Hecke action on the special fibre is additive
-- statement:
--   Fix natural numbers $p$, $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a divisibility $p \mid M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, and assume the residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed. Let $\Lambda$ be level data for $(p, M, H, A)$, that is, a morphism $\sigma_A \colon \operatorname{Spec} A \to \mathrm{base}\,p$ with $\mathrm{barPt}\,A$ followed by $\sigma_A$ equal to $\mathrm{genPt}\,p$, together with a scheme over $\mathrm{base}\,p$ carrying a relative group law and pinnings of its generic and special points, and let $O$ be a Néron object over $\Lambda$: a smooth, separated, surjective, quasi-compact morphism $g \colon G \to \mathrm{base}\,p$ of locally finite type with preconnected fibres, a commutative relative group law, an additive Galois-equivariant bijection $\mathrm{pts} \colon J_H(M) \simeq$ sections of $g$ over $\mathrm{genPt}\,p$, endomorphisms $\mathrm{hecke}\,S\,t$ of $g$ over $\mathrm{base}\,p$ compatible with the group law on $T$-points and with the Hecke action on $\mathrm{pts}$, flat surjective multiplication-by-$n$ maps, and the bijection $O.\mathrm{ptsSp}$ between $\mathrm{GluedPic}^0(\kappa, \mathrm{Fbar}\,p\,M\,H\,\kappa, O.\mathrm{ssFinset})$ — the quotient of admissible divisors by glued principal ones for the finset $O.\mathrm{ssFinset}$ of pairs of places of the $q$-expansion function field $\mathrm{Fbar}$ — and the sections of $g$ over $\mathrm{resPt}\,A$ followed by $\sigma_A$. Then for every set $S$ of naturals and every generator $t$ of $\mathrm{CohCarrier.Gen}\,M\,S$ (one of $T_\ell$ with $\ell$ prime, $\ell \notin S$, $\ell \nmid M$; $U_q$ with $q$ prime dividing $M$; or $\langle d \rangle$ with $d \in (\mathbb{Z}/M)^{\times}$) there is an additive monoid homomorphism $\Phi$ of $\mathrm{GluedPic}^0(\kappa, \mathrm{Fbar}\,p\,M\,H\,\kappa, O.\mathrm{ssFinset})$ into itself with $\Phi(\xi) = O.\mathrm{ptsSp}^{-1}\bigl(O.\mathrm{ptsSp}(\xi) \text{ composed with } O.\mathrm{hecke}\,S\,t\bigr)$ for every $\xi$.
--
--   This records that the endomorphism of the special fibre induced by a Hecke or diamond generator, read through the dictionary between the glued degree-zero divisor class group of the reduced modular curve and the points of the Néron object, respects the group structure. It is the additivity statement used when identifying these transported operators with explicit maps on glued Picard groups, in particular for the diamond operators, the $U_q$ operator on node units, and the comparison with degeneracy pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S : Set ℕ) (t : CohCarrier.Gen M S) :
    ∃ Φ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+
        GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      ∀ ξ, Φ ξ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S t)) := by sorry
