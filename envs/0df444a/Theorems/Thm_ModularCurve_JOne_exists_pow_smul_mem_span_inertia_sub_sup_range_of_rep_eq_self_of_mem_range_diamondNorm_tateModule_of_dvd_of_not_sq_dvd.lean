-- Prove2me | Theorems.Thm_ModularCurve_JOne_exists_pow_smul_mem_span_inertia_sub_sup_range_of_rep_eq_self_of_mem_range_diamondNorm_tateModule_of_dvd_of_not_sq_dvd
-- name    : ModularCurve.JOne.exists_pow_smul_mem_span_inertia_sub_sup_range_of_rep_eq_self_of_mem_range_diamondNorm_tateModule_of_dvd_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/578ed2b6-bb42-5093-b088-d95414a838cf
-- title:
--   Inertia-invariant diamond-norm vectors in TₚJ₁(M) modulo monodromy and old parts
-- statement:
--   Fix $M \ge 1$ and a prime $p$, and suppose the level-$M$ Hecke–diamond input package [`ModularCurve.HeckeDiamondInputsAll M`](def/ModularCurve_X1HeckeModule.html#L58) holds (Hecke inputs along every prime, and for every $d$ coprime to $M$ a diamond automorphism of the function field of $X_1(M)$ over $\mathbb{Q}$ together with a base change of it over $\overline{\mathbb{Q}}$) as well as the commutation hypothesis [`ModularCurve.HeckeDiamondCommuteBar M`](def/ModularCurve_X1HeckeModule.html#L54) saying that the generators $T_\ell$ and $\langle d\rangle$ act on $J_1(M)$ pairwise commutingly; let $q$ be a prime with $q \ne p$, $q \mid M$ and $q^2 \nmid M$, and assume the same two packages at level $M/q$; let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$. Here $J_1(M)$ is the group of degree-zero divisor classes of the base change to $\overline{\mathbb{Q}}$ of the Laurent-series model of the function field of $X_1(M)$, $T_p$ of it is the group of sequences $(x_n)$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, and the Hecke–diamond algebra acts on $T_p$ through the module structures [`ModularCurve.heckeModuleOneBar`](def/ModularCurve_X1HeckeModule.html#L129) at levels $M$ and $M/q$. The assertion is that there exist $\mathbb{Z}_p$-linear maps $\alpha, \beta : T_p J_1(M/q) \to T_p J_1(M)$, each commuting with the images of the generators $T_\ell$ and $\langle \ell\rangle$ for every prime $\ell \nmid M$ (levels $M/q$ on the source, $M$ on the target), an element $\sigma_0$ of the inertia subgroup of $P$ inside $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ (the image of the inertia subgroup of the decomposition subgroup), and an exponent $k \in \mathbb{N}$, such that every $x \in T_p J_1(M)$ lying in the range of the diamond norm $\sum_d \langle d\rangle$, the sum being over $d < M$ with $d$ coprime to $M$ and $d \equiv 1 \pmod{M/q}$, and satisfying $\sigma_0 x = x$ for the Galois action on $T_p J_1(M)$, obeys $$p^k x \in \operatorname{span}_{\mathbb{Z}_p}\{\sigma y - y : \sigma \in I_P,\ y \in T_p J_1(M)\} + \operatorname{im}\alpha + \operatorname{im}\beta.$$
--
--   This is the arithmetic input from Grothendieck's description of the $p$-adic Tate module of a semistable Jacobian at a prime $q$ of multiplicative reduction: inertia invariants in the diamond-norm part of $T_pJ_1(M)$ are, up to a bounded power of $p$, accounted for by the monodromy submodule together with the two degeneracy images from level $M/q$. It feeds the statement, for a primitive form whose conductor is not divisible by $q$, that some inertia element at $q$ moves a suitable vector out of the span of the monodromy and old parts, which is the step in Ribet's level-lowering argument where $q$ is removed from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_exists_pow_smul_mem_span_inertia_sub_sup_range_of_rep_eq_self_of_mem_range_diamondNorm_tateModule_of_dvd_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.exists_pow_smul_mem_span_inertia_sub_sup_range_of_rep_eq_self_of_mem_range_diamondNorm_tateModule_of_dvd_of_not_sq_dvd
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hin' : ModularCurve.HeckeDiamondInputsAll (M / q))
    (hcomm' : ModularCurve.HeckeDiamondCommuteBar (M / q))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q) :
    letI := ModularCurve.heckeModuleOneBar M
    letI := ModularCurve.heckeModuleOneBar (M / q)
    ∃ (α β : TateModule p (ModularCurve.JOne (M / q)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
        α ∘ₗ ModularCurve.tateHeckeRepOne p (ModularCurve.JOne (M / q))
            (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩) =
          ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩) ∘ₗ α ∧
        α ∘ₗ ModularCurve.tateHeckeRepOne p (ModularCurve.JOne (M / q)) (ModularCurve.diamondGen ℓ) =
          ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) (ModularCurve.diamondGen ℓ) ∘ₗ α ∧
        β ∘ₗ ModularCurve.tateHeckeRepOne p (ModularCurve.JOne (M / q))
            (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩) =
          ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩) ∘ₗ β ∧
        β ∘ₗ ModularCurve.tateHeckeRepOne p (ModularCurve.JOne (M / q)) (ModularCurve.diamondGen ℓ) =
          ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) (ModularCurve.diamondGen ℓ) ∘ₗ β) ∧
      ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ∃ k : ℕ,
        ∀ x : TateModule p (ModularCurve.JOne M),
          x ∈ LinearMap.range
              (∑ d ∈ (Finset.range M).filter (fun d => Nat.Coprime d M ∧ d ≡ 1 [MOD M / q]),
                ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) (ModularCurve.diamondGen d)) →
          TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ₀ x
              = x →
          ((p : ℤ_[p]) ^ k) • x ∈
            Submodule.span ℤ_[p]
                {z : TateModule p (ModularCurve.JOne M) |
                  ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∃ y : TateModule p (ModularCurve.JOne M),
                    z = TateModule.rep p (ModularCurve.JOne M)
                          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y - y} ⊔
              LinearMap.range α ⊔ LinearMap.range β := by sorry
