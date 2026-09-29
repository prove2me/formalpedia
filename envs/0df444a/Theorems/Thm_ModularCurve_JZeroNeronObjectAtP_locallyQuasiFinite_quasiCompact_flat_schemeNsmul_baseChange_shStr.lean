-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange_shStr
-- name    : ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange_shStr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/1214f8a6-7aa4-5916-95c5-291a7e1ac77d
-- title:
--   Flatness and local quasi-finiteness of [m] after base change
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime and non-zero, and assume $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure of $\mathbf{Q}$ which lies over $p$, in the sense that the image of $p$ in the field is a non-unit of $A$. Let $\Lambda$ be a term of `JZeroNeronObjectAtP.LevelData N₀ p A`, that is, a section $\sigma_A$ of the base scheme `base p` over $\operatorname{Spec} A$ compatible with the generic point, a scheme $X$ with a structure morphism $f$ to `base p`, a relative group law $\Lambda.L$ for $f$ over `baseRing p`, and bijections identifying $J_0(N_0)$-points and their reductions with sections of $f$ over the generic and the residual points; assume $\Lambda$ satisfies `IsJacobian` (commutativity of $\Lambda.L$, additivity and Galois equivariance of the point parametrisations, agreement of reductions, Hecke equivariance, and the abelian-scheme property bundle for $f$). Let $O$ be a term of `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, whose data include a scheme $G$ with structure morphism $O.g$ to `base p`, a relative group law $O.L$ for $O.g$, a parametrisation of $J_0(N_0p)$ by sections over the generic point, and the smoothness, separatedness, finite-type, quasi-compactness, surjectivity, fibrewise preconnectedness, flatness and surjectivity of $[n]$ for $n>0$, and generic properness axioms. Let $m>0$. Then the endomorphism $[m]$ determined by the base change of the group law $O.L$ along $\Lambda.\mathrm{shStr}\colon \mathrm{shBase}\,A \to \mathrm{base}\,p$ (the morphism of spectra induced by $\Lambda.\mathrm{baseToSh}$), namely the underlying scheme morphism of the $m$-fold multiple of the identity section, is locally quasi-finite, quasi-compact and flat.
--
--   This is the statement, after base change from `base p` to the strictly henselian base `shBase A`, that multiplication by $m$ on the identity component of the Néron model of $J_0(N_0p)$ is locally quasi-finite, quasi-compact and flat; the three properties are inherited from the corresponding assertion over `base p`, where flatness is an axiom of the Néron object and local quasi-finiteness comes from quasi-finiteness of the kernel $G[m]$ on the generic fibre, where $m$ is invertible. It is used by [`ModularCurve.JZeroNeronObjectAtP.NeronExtension.locallyQuasiFinite_quasiCompact_flat_schemeNsmul`](thm.html#ModularCurve.JZeroNeronObjectAtP.NeronExtension.locallyQuasiFinite_quasiCompact_flat_schemeNsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange_shStr.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange_shStr
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyQuasiFinite ((O.L.baseChange Λ.shStr).schemeNsmul m) ∧
      QuasiCompact ((O.L.baseChange Λ.shStr).schemeNsmul m) ∧ Flat ((O.L.baseChange Λ.shStr).schemeNsmul m) := by sorry
