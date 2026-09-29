-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw
-- name    : ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/d20cf845-ec8f-5216-a7c5-4a9c6e963543
-- title:
--   Local quasi-finiteness of m-torsion in the degeneracy kernel
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure of $\mathbf Q$ that lies over $p$, in the sense that the image of $p$ belongs to the non-units of $A$, let $\Lambda$ be a `LevelData` for $N_0$, $p$ and $A$ — in particular a scheme $X$ with a morphism $\Lambda.f$ to the base of $p$, a relative group law $\Lambda.L$ on it, a structural morphism $\Lambda.\sigma_A \colon \operatorname{Spec} A \to$ the base, and bijections between the groups $J^0$ at level $N_0$ over the generic and special points and the sections of $\Lambda.f$ there — and assume $\Lambda$ satisfies `IsJacobian`. Let $O$ be a `JZeroNeronObjectAtP` for these data, with underlying morphism $O.g$, relative group law $O.L$ and two degeneracy morphisms $O.\mathrm{degeneracyHom}\,i$, $i \in \{0,1\}$, from $O.g$ to $\Lambda.f$ over the base, each compatible with the group laws. Let $m > 0$. Base-change $O.L$ and $\Lambda.L$ along $\Lambda.\sigma_A$, and restrict the two degeneracy morphisms along $\Lambda.\sigma_A$ via `fibreRestrictAlong`; these restrictions are homomorphisms of the base-changed laws. Form the relative group law `kerPairLaw` on the joint kernel of the two restricted degeneracy morphisms over $\operatorname{Spec} A$. The assertion is that for this law the structure morphism `schemeKerStr m` of the $m$-torsion kernel scheme — the second projection of the pullback of the multiplication-by-$m$ morphism along the unit section — is locally quasi-finite over $\operatorname{Spec} A$.
--
--   This is the local quasi-finiteness input for the $m$-torsion of the joint kernel $\mathcal H_A$ of the two degeneracy maps on the Néron model over the valuation ring $A$; it is what allows the kernel's torsion to be treated fibrewise. It is used in the finiteness and cardinality estimates for kernel coset representatives and in the bound by a power of the toric rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    letI LHA := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange Λ.σA) (Λ.L.baseChange Λ.σA)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i))
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong Λ.σA
        (fun t x y => O.degeneracyHom_mul i t x y))
    LocallyQuasiFinite (LHA.schemeKerStr m) := by sorry
