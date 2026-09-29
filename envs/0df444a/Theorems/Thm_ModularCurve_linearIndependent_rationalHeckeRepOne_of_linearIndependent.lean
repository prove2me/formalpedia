-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent
-- name    : ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/31be6df5-fdff-52f5-91bd-8a24ddc17dd4
-- title:
--   Hecke faithfulness on the rational Tate module of J₁(M)
-- statement:
--   Let $M$ be a nonzero natural number and $p$ a prime. Assume [`ModularCurve.HeckeDiamondInputsAll M`](def/ModularCurve_X1HeckeModule.html#L58), i.e. that for every prime $\ell$ the input predicate `HeckeInputsOneAlong` holds for the algebraic closure $\overline{\mathbb Q}$, the level $M$ and $\ell$, and that for every $d$ coprime to $M$ there is an automorphism of the function field `x1FunctionField M` of $X_1(M)$ over $\mathbb Q$ satisfying the diamond characterisation `IsDiamondAut M d` (normalised $q$-expansion identity against slashes by matrices in $\Gamma_0(M)$ with upper-left entry $\equiv d$), together with an automorphism of the base-changed field `x1FunctionFieldBar M` over $\overline{\mathbb Q}$ which is a base change of `diamondAut M d`. Assume also [`ModularCurve.HeckeDiamondCommuteBar M`](def/ModularCurve_X1HeckeModule.html#L54): the endomorphisms of $J =$ `JOne M`, the group of degree-zero divisor classes of `x1FunctionFieldBar M` modulo principal divisors, given by the Hecke operators `heckeOperatorOneBar` at primes and the diamond operators `diamondOneBar`, commute pairwise. Hence the polynomial ring $\mathbb T = \mathbb Z[\,$`Nat.Primes`$\,\oplus\,\mathbb N\,]$ (`HeckeAlgOne`) acts on $J$ through the instance `heckeModuleOneBar M`, which sends the generators to these operators. Let $t : \iota \to \mathbb T$ be a family whose images in $\mathbb T/\operatorname{Ann}_{\mathbb T}(J)$ are $\mathbb Z$-linearly independent. Then the family of induced $\mathbb Q_p$-endomorphisms `rationalHeckeRepOne p J (t i)` of $\mathbb Q_p \otimes_{\mathbb Z_p} T_p J$, where $T_p J$ consists of the sequences $(x_n)$ in $J$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, is $\mathbb Q_p$-linearly independent.
--
--   This is the faithfulness statement for the Hecke–diamond action on the $p$-adic Tate module of the Jacobian of $X_1(M)$: equivalently, $(\mathbb T/\operatorname{Ann}_{\mathbb T}(J_1(M)))\otimes\mathbb Q_p \to \operatorname{End}_{\mathbb Q_p}(V_p J_1(M))$ is injective, the case $A = J_1(M)$ of the injectivity of $\operatorname{End}(A)\otimes\mathbb Z_p \to \operatorname{End}(T_p A)$ for abelian varieties. It is used to transfer eigenform data from $J_1(M)$ to its rational Tate module, in the construction of eigenvalue homomorphisms on the rational Hecke algebra in [`CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq`](thm.html#CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent (M p : ℕ) [NeZero M]
    [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    {ι : Type} (t : ι → ModularCurve.HeckeAlgOne)
    (hli : letI := ModularCurve.heckeModuleOneBar M
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlgOne (ModularCurve.JOne M)) (t i))) :
    letI := ModularCurve.heckeModuleOneBar M
    LinearIndependent ℚ_[p]
      (fun i => ModularCurve.rationalHeckeRepOne p (ModularCurve.JOne M) (t i)) := by sorry
