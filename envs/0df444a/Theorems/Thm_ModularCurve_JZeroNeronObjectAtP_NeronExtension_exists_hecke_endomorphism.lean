-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hecke_endomorphism
-- name    : ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_hecke_endomorphism
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/1328804a-6925-5b97-9c26-712555989d2e
-- title:
--   Hecke operators extend to the Néron model over O_A
-- statement:
--   Fix a natural number $N_0$ with $N_0\neq 0$ and a prime $p$ with $p\nmid N_0$, and let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ lying over $p$ in the sense that $p$ belongs to the nonunits of $A$. Let $\Lambda$ be a `LevelData` for $(N_0,p,A)$ — a scheme $X$ over `base p` with a relative group law and bijections between $J_0(N_0)$-points, i.e. $\mathrm{Pic}^0$ of the level-$N_0$ modular function field over $\overline{\mathbf{Q}}$, and sections over the generic point, and similarly over the residue point — assumed to satisfy `IsJacobian`; let $O$ be a `JZeroNeronObjectAtP` over $\Lambda$ (a smooth, separated, quasi-compact group scheme $g\colon G\to$ `base p` with connected fibres together with a points dictionary for $J_0(N_0p)$ and a Hecke field), and let $F$ be a `NeronExtension` of $O$, so $g_N\colon$ `Nfull` $\to$ `shBase A` carries a relative group law and the Néron model property bundle over the ring `shRing A` with fraction field `invField A`, and an open immersion of the base change of $O$'s group scheme into `Nfull`. Equip $J_0(N_0p)(\overline{\mathbf{Q}})$ with the `HeckeAlg`-module structure `heckeModuleBar (N₀ * p)`, where `HeckeAlg` is the polynomial ring $\mathbf{Z}[x_\ell : \ell \text{ prime}]$. The assertion is that for every $t\in$ `HeckeAlg` there is a morphism $\varphi\colon$ `Nfull` $\to$ `Nfull` over `shBase A` such that for every $x\in J_0(N_0p)(\overline{\mathbf{Q}})$ the point `F.ptsN (t • x)` (the lift of $O$'s point of $x$ to the base change, followed by the open immersion) equals `F.ptsN x` followed by $\varphi$. Only this compatibility on points is asserted: unlike the `hecke` field of `JZeroNeronObjectAtP`, no additivity of $\varphi$ for the group law is claimed.
--
--   This is the statement that each Hecke operator on $J_0(N_0p)$ is induced, on $\overline{\mathbf{Q}}$-points, by an endomorphism of the Néron model over the valuation ring of the inertia field at $A$; it is the form of the Néron mapping property that the descent of the Hecke action to the component group uses. It feeds the assembly of the ordinary-case data object [`ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hecke_endomorphism.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_hecke_endomorphism
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    letI := heckeModuleBar (N₀ * p)
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver F.gN F.gN, ∀ x : JZero (N₀ * p), (F.ptsN (t • x)).1 = (F.ptsN x).1 ≫ φ.1 := by sorry
