-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_galois_smul
-- name    : ModularCurve.JZeroNeronObjectAtP.NeronExtension.extN_galois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/bf1125fd-0cd1-50e1-a3c3-5b8759fada12
-- title:
--   Decomposition-group stability of A-extendable points
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ lying over $p$, in the sense that $p$ is a nonunit of $A$, let $\Lambda$ be a level datum `LevelData N₀ p A` — a structure morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` restricting along `barPt A` to the generic point `genPt p`, a scheme $X$ over `base p` with a relative group law, and bijections between $\mathrm{JZero}\,N_0$ (the degree-zero divisor class group of the level-$N_0$ modular function field over $\overline{\mathbf{Q}}$) and the sections over `genPt p`, and between the corresponding group over the residue field of $A$ and the sections over the reduction point — and assume $\Lambda$ satisfies `IsJacobian` (abelian-scheme properties, commutativity, additivity and Galois equivariance of the points dictionary, compatibility of reduction, and Hecke equivariance). Let $O$ be a `JZeroNeronObjectAtP` for these data and $F$ a `NeronExtension` of $O$, i.e. a commutative relative group scheme over `shBase A` with the Néron model property over `shRing A` with fraction field `invField A`, containing the base change of $O$ as an open subgroup scheme, together with a specialisation map to the component group. The assertion is: for every $\sigma$ in the decomposition subgroup of $A$ inside $\operatorname{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ and every $x \in \mathrm{JZero}(N_0 p)$, if `F.ExtN x` holds — that is, the point `F.ptsN x` factors as `barPt A` followed by some section of `F.gN` over `shPt A` — then `F.ExtN (σ • x)` holds as well.
--
--   This records that the subgroup of points of $J_0(N_0p)(\overline{\mathbf{Q}})$ extending to integral sections of the Néron model over the valuation ring of the inertia field is stable under the decomposition group at $p$, the uniqueness of Néron models over the base turning a $\sigma$-twisted section into a section of the same model. It is used in the construction of the ordinary-reduction data at $p$ assembled in [`ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_galois_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.extN_galois_smul
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x : JZero (N₀ * p), F.ExtN x → F.ExtN (σ • x) := by sorry
