-- Prove2me | Theorems.Thm_ModularCurve_JOne_diamondOneBar_smul_smul_sub_self_eq_smul_heckeOperatorOneBar_of_isFrobeniusAt_of_eq_sum_diamondOneBar
-- name    : ModularCurve.JOne.diamondOneBar_smul_smul_sub_self_eq_smul_heckeOperatorOneBar_of_isFrobeniusAt_of_eq_sum_diamondOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e82e8389-97ad-5dde-b529-a4119e6fceae
-- title:
--   Frobenius at q acting as q U_q on J₁(M₀q)
-- statement:
--   Let $M_0$ be a non-zero natural number and $q$ a prime not dividing $M_0$, and write $M=M_0q$. Assume [`ModularCurve.HeckeDiamondInputsAll`](def/ModularCurve_X1HeckeModule.html#L58) at level $M$: the predicate `HeckeInputsOneAlong` over $\overline{\mathbb Q}$ holds at every prime $\ell$, and for every $d$ coprime to $M$ there exists an automorphism of the $q$-expansion function field `x1FunctionField M` over $\mathbb Q$ satisfying `IsDiamondAut M d` together with an automorphism of the base-changed field `x1FunctionFieldBar M` over $\overline{\mathbb Q}$ which is a base-change automorphism of `diamondAut M d` in the sense of `IsBaseChangeAutOf`. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, let $\sigma$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ lying in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$, and let $\tau$ be an element of the decomposition subgroup of $P$ inducing $x\mapsto x^{q}$ on the residue field of $P$. Let $x$ be an element of $J_1(M)=\mathrm{Pic}^0(\overline{\mathbb Q},\,\mathrm{x1FunctionFieldBar}\ M)$ annihilated by some integer $n$ with $q\nmid n$, and put $y=\sum_{d}\langle d\rangle x$, the sum of `diamondOneBar M d` applied to $x$ over the $d<M$ coprime to $M$ with $d\equiv 1 \pmod{M_0}$. Finally let $d_1$ be coprime to $M$ with $d_1\equiv q\pmod{M_0}$. Then $\langle d_1\rangle\bigl(\tau\cdot(\sigma\cdot y-y)\bigr)=q\cdot T_q(\sigma\cdot y-y)$, where $\langle d_1\rangle$ is `diamondOneBar M d₁` and $T_q$ is `heckeOperatorOneBar M q`, the Galois action on $J_1(M)$ being the one induced coefficientwise on degree-zero divisor classes.
--
--   This is the Frobenius half of Ribet's local description at $q$ of the Galois action on the prime-to-$q$ torsion of $J_1(M_0q)$ coming from the curve $X(\Gamma_1(M_0)\cap\Gamma_0(q))$: on differences $\sigma y-y$ produced by inertia from the diamond-norm part, a Frobenius at $q$ acts as $q\,U_q$ up to the diamond operator at $q$. It feeds the computation of the characteristic polynomial of Frobenius for the $q$-adic representations attached to weight-two newforms of level divisible exactly once by $q$ with nebentypus unramified at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_diamondOneBar_smul_smul_sub_self_eq_smul_heckeOperatorOneBar_of_isFrobeniusAt_of_eq_sum_diamondOneBar.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.diamondOneBar_smul_smul_sub_self_eq_smul_heckeOperatorOneBar_of_isFrobeniusAt_of_eq_sum_diamondOneBar
    (M₀ q : ℕ) [NeZero M₀] (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀)
    (hin : ModularCurve.HeckeDiamondInputsAll (M₀ * q))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : P.IsFrobeniusAt τ q)
    (x : ModularCurve.JOne (M₀ * q)) (n : ℕ) (hn : ¬ q ∣ n) (hx : (n : ℤ) • x = 0)
    (y : ModularCurve.JOne (M₀ * q))
    (hy : y = ∑ d ∈ (Finset.range (M₀ * q)).filter (fun d => Nat.Coprime d (M₀ * q) ∧ d ≡ 1 [MOD M₀]),
            ModularCurve.diamondOneBar (M₀ * q) d x)
    (d₁ : ℕ) (hd₁ : Nat.Coprime d₁ (M₀ * q)) (hd₁q : d₁ ≡ q [MOD M₀]) :
    ModularCurve.diamondOneBar (M₀ * q) d₁ (τ • (σ • y - y)) =
      (q : ℤ) • ModularCurve.heckeOperatorOneBar (M₀ * q) ⟨q, hq⟩ (σ • y - y) := by sorry
