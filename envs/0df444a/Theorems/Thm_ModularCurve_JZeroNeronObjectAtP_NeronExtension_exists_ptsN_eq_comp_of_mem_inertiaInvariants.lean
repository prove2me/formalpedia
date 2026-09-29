-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants
-- name    : ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_ptsN_eq_comp_of_mem_inertiaInvariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/1c9530f3-4ea6-5bd0-bf11-ed69c5db8c07
-- title:
--   Inertia-invariant points give sections of the Néron extension
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and $p \nmid N_0$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, i.e. $p$ lies in the non-units of $A$. Let $\Lambda$ be a level datum `LevelData N₀ p A`, assumed to satisfy `Λ.IsJacobian`, let $O$ be a Néron object `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ` at level $N_0p$, and let $F$ be a Néron extension of $O$, so that $F$ provides a group scheme $F.gN : \mathrm{Nfull} \to \mathrm{shBase}\,A = \operatorname{Spec} (\mathtt{shRing}\,A)$ with the Néron model property bundle over $\mathtt{shRing}\,A$ with fraction field $\mathtt{invField}\,A$, together with an open immersion from the base change of $O.g$. The assertion is: for every $x$ in $J_0(N_0p) = \mathrm{Pic}^0$ of the level-$N_0p$ modular function field over $\overline{\mathbb{Q}}$ which lies in `inertiaInvariants A (N₀ * p)`, that is, is fixed by every element of the inertia subgroup `A.inertiaSubgroupIn ℚ`, there exists a section $s$ of $F.gN$ over the identity of $\mathrm{shBase}\,A$ (a morphism $s$ with $s$ followed by $F.gN$ the identity) such that the $\overline{\mathbb{Q}}$-point $F.\mathtt{ptsN}\,x$ — the image under the open immersion of the lift of $O.\mathtt{pts}\,x$ — equals the composite $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} A \to \mathrm{shBase}\,A$ followed by $s$.
--
--   This is the descent step turning an inertia-invariant $\overline{\mathbb{Q}}$-point of $J_0(N_0p)$ into an integral section of the Néron extension over the base $\operatorname{Spec}(\mathtt{shRing}\,A)$, the classical combination of Galois descent for points of a separated scheme with the Néron mapping property. It feeds the construction of finiteness statements for the points $F.\mathtt{ptsN}$, used by [`ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_isFinite_forall_ptsN_comp_eq_of_hopf`](thm.html#ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_isFinite_forall_ptsN_comp_eq_of_hopf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_ptsN_eq_comp_of_mem_inertiaInvariants
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    ∀ x : JZero (N₀ * p), x ∈ inertiaInvariants A (N₀ * p) →
      ∃ s : SchemeHomOver (𝟙 (shBase A)) F.gN, (F.ptsN x).1 = (barPt A ≫ shPt A) ≫ s.1 := by sorry
