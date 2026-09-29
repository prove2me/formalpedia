-- Prove2me | Theorems.Thm_ModularCurve_reductionModL_heckeOperatorBar
-- name    : ModularCurve.reductionModL_heckeOperatorBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/5d18e9e6-2502-526e-80b7-9020cbefabc7
-- title:
--   Eichler–Shimura congruence for the reduction map on J₀(N)
-- statement:
--   Let $N\ge 1$ and let $\ell$ be a prime not dividing $N$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $\ell$ in the sense of `LiesOverPrime`, i.e. the image of $\ell$ in $\overline{\mathbb Q}$ is a nonunit of $A$, and suppose the residue field $k_A=\mathrm{ResidueField}(A)$ has characteristic $\ell$. Assume the predicate [`ModularCurve.ReductionInputsModL A N`](def/ModularCurve_ReductionModL.html#L184), that is, `ReductionInputsAlong` for the residue map $A\to k_A$: there is a map $r$ on places of the base-changed modular function field over $\overline{\mathbb Q}$ satisfying `IsPlaceReductionAlong` together with `PrincipalGeneratedByIntegral`, the data out of which the additive map $\mathrm{red}_A=$ `reductionModL A N` from $J_0(N)=\mathrm{Pic}^0$ of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$ to `JZeroC k_A N` $=\mathrm{Pic}^0$ of `modularFunctionFieldFullC k_A N` over $k_A$ is built (the map is $0$ when these inputs fail). Then for every class $z\in$ `JZero N`,
--   $$\mathrm{red}_A\bigl(T_\ell z\bigr)=\bigl(\mathrm{Fr}_*+\mathrm{Fr}^*\bigr)\bigl(\mathrm{red}_A z\bigr),$$
--   where $T_\ell=$ `heckeOperatorBar N ⟨ℓ, _⟩` is the $\mathbb Z$-linear endomorphism of `JZero N` coming from `heckeOperatorAlong` at $\ell$, and the right-hand operator is `heckeOperatorModL k_A N ℓ`, by definition the sum `frobeniusPushforwardModL` $+$ `frobeniusPullbackModL` on `JZeroC k_A N`.
--
--   This is the Eichler–Shimura congruence relation $T_\ell \equiv \mathrm{Fr}_* + \mathrm{Fr}^*$ in the form of an exact intertwining identity between the Hecke operator on the Jacobian of $X_0(N)$ in characteristic $0$ and the Frobenius pushforward plus pullback on the reduction at a place above $\ell \nmid N$. It is the source of the characteristic polynomial of Frobenius acting on the $\ell$-adic Tate module of $J_0(N)$, and is used downstream in the analysis of Galois representations attached to newforms and of the Hecke action on torsion of the reduced Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reductionModL_heckeOperatorBar.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeOperatorModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.reductionModL_heckeOperatorBar (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ] (h : ModularCurve.ReductionInputsModL A N)
    (z : ModularCurve.JZero N) :
    ModularCurve.reductionModL A N (ModularCurve.heckeOperatorBar N ⟨ℓ, Fact.out⟩ z) =
      ModularCurve.heckeOperatorModL (IsLocalRing.ResidueField A) N ℓ
        (ModularCurve.reductionModL A N z) := by sorry
