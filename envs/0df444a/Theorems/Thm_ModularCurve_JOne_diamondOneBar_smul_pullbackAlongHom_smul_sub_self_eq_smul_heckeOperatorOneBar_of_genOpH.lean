-- Prove2me | Theorems.Thm_ModularCurve_JOne_diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH
-- name    : ModularCurve.JOne.diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/88407c7c-6735-5637-889b-cb92d576499b
-- title:
--   Transport of the Γ_H-level relation to J₁(M₀q)
-- statement:
--   Fix natural numbers $M_0 \neq 0$ and a prime $q$ with $q \nmid M_0$, and let $M = M_0 q$. Assume `HeckeDiamondInputsAll M`, i.e. that for every prime $\ell$ the data defining the degree-zero Hecke correspondence at level $M$ are available, and that for every $d$ coprime to $M$ a diamond automorphism $\langle d\rangle$ of the function field `x1FunctionField M` exists together with a base change of it to $\overline{\mathbb{Q}}$. Let $\iota$ be an $\overline{\mathbb{Q}}$-algebra map from the base change to $\overline{\mathbb{Q}}$ of the field $F(\Gamma_1(M_0)\cap\Gamma_0(q)) \subset \mathbb{Q}((q))$ into `x1FunctionFieldBar M`, which on underlying Laurent series is the identity (hypothesis `hι`), which is integral (`hint`) and for which the fundamental identity $\sum_{w \mid v} e_w \deg w = [F':F]\deg v$ holds along $\iota$ (`hFI`); `HasPrincipalDivisors` is assumed for `x1FunctionFieldBar M`. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q \in P^{\mathrm{nonunits}}$, let $\sigma$ lie in the image of the inertia subgroup of $P$ over $\mathbb{Q}$, and let $\tau$ lie in the decomposition subgroup of $P$ and act on the residue field of $P$ by $x \mapsto x^q$. Let $z$ be a class in the degree-zero divisor class group of the base-changed field $F(\Gamma_1(M_0)\cap\Gamma_0(q))\cdot\overline{\mathbb{Q}}$, annihilated by some $n$ with $q \nmid n$. Let $d_1$ be coprime to $M$ with $d_1 \equiv q \pmod{M_0}$, and let $S$ be a set of naturals. Assume the corresponding relation at level $\Gamma_H(M)$ for $H$ the preimage of the trivial subgroup under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/M_0)^\times$: for every class $z'$ in $J_H(M) = \mathrm{Pic}^0$ of `xHFunctionFieldBar M H` and every $n'$ with $q \nmid n'$ and $n' z' = 0$, the diamond operator at $d_1$ applied to $\tau\cdot(\sigma z' - z')$ equals $q$ times the Hecke operator at $q$ applied to $\sigma z' - z'$ (both taken as the values of `genOpH` on the generators `dia` and `U q`). The conclusion is the same relation on $J_1(M) = \mathrm{Pic}^0($`x1FunctionFieldBar M`$)$ for the pulled-back class: $\langle d_1\rangle\bigl(\tau\cdot \iota^*(\sigma z - z)\bigr) = q\, T_q\bigl(\iota^*(\sigma z - z)\bigr)$, where $\langle d_1\rangle$ is the action of the base-changed diamond automorphism `diamondAutBar M d₁`, $T_q$ is `heckeOperatorOneBar M ⟨q, hq⟩`, and $\iota^*$ is the map on degree-zero divisor classes induced by divisor pull-back along $\iota$.
--
--   This is the transport step passing the relation $\langle d_1\rangle(\tau(\sigma z - z)) = q\,U_q(\sigma z - z)$ on prime-to-$q$ torsion from level $\Gamma_H(M_0q)$, with $H$ the kernel of $(\mathbb{Z}/M_0q)^\times \to (\mathbb{Z}/M_0)^\times$ (so that $\Gamma_H(M_0q) = \Gamma_1(M_0)\cap\Gamma_0(q)$), to level $\Gamma_1(M_0q)$ along the pull-back induced by the inclusion of function fields; it rests on the compatibility of the forgetful map with diamond operators and with the degeneracy maps defining the operator at $q$. It is used by [`ModularCurve.JOne.diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_isFrobeniusAt`](thm.html#ModularCurve.JOne.diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_isFrobeniusAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JOne.diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH
    (M₀ q : ℕ) [NeZero M₀] (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀)
    (hin : ModularCurve.HeckeDiamondInputsAll (M₀ * q))
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M₀ * q))]
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q))
        →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M₀ * q)))
    (hι : ∀ x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q),
      ((ι x : ModularCurve.x1FunctionFieldBar (M₀ * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral)
    (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : P.IsFrobeniusAt τ q)
    (z : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q)))
    (n : ℕ) (hn : ¬ q ∣ n) (hz : (n : ℤ) • z = 0)
    (d₁ : ℕ) (hd₁ : Nat.Coprime d₁ (M₀ * q)) (hd₁q : d₁ ≡ q [MOD M₀])

    (S : Set ℕ)
    (hJH : ∀ (z' : JH (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))))
        (n' : ℕ), ¬ q ∣ n' → (n' : ℤ) • z' = 0 →
      genOpH (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) S
          (CohCarrier.Gen.dia (ZMod.unitOfCoprime d₁ hd₁)) (τ • (σ • z' - z')) =
        (q : ℤ) • genOpH (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) S
          (CohCarrier.Gen.U q hq (Dvd.intro_left M₀ rfl)) (σ • z' - z')) :
    ModularCurve.diamondOneBar (M₀ * q) d₁
        (τ • AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (σ • z - z)) =
      (q : ℤ) • ModularCurve.heckeOperatorOneBar (M₀ * q) ⟨q, hq⟩
        (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (σ • z - z)) := by sorry
