-- Prove2me | Theorems.Thm_ModularCurve_rep_frobenius_rep_heckeGenOne_sub_smul_rep_diamondGen_rep_inertia_sub_eq_zero_normFreePartAt_tateModule_jOne_of_le_div
-- name    : ModularCurve.rep_frobenius_rep_heckeGenOne_sub_smul_rep_diamondGen_rep_inertia_sub_eq_zero_normFreePartAt_tateModule_jOne_of_le_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/61eeceb4-4edc-57ba-a79d-db642d20dea0
-- title:
--   Frobenius and T_q on the norm-free part of TₚJ₁(M)
-- statement:
--   Let $M\ge 1$, let $p$ be a prime and $q$ a prime with $q\mid M$ but $q^2\nmid M$, assume $5\le M/q$ and $p\ne q$, and assume the predicate [`ModularCurve.HeckeDiamondCommuteBar M`](def/ModularCurve_X1HeckeModule.html#L54), i.e. that the operators `heckeDiamondGenBar M i`, indexed by $i\in\mathrm{Primes}\sqcup\mathbb{N}$, commute pairwise. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ belongs to the nonunits of $P$; let $\sigma$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ lying in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$, and let $\tau$ be a Frobenius at $P$ for $q$, i.e. $\tau$ lies in the decomposition subgroup of $P$ and acts on the residue field of $P$ by $x\mapsto x^{q}$. Let $u\in\mathbb{N}$ satisfy $u\equiv 1 \pmod{M/q}$ and suppose $\sigma\zeta=\zeta^{u}$ for every $\zeta\in\overline{\mathbb{Q}}$ with $\zeta^{q}=1$. Let $y$ lie in the $p$-adic Tate module of $\mathrm{JOne}(M)=\mathrm{Pic}^{0}$ of the base-changed function field of $X_1(M)$ over $\overline{\mathbb{Q}}$, that is, a sequence $(y_n)$ with $p^{n}y_n=0$ and $p\,y_{n+1}=y_n$, and suppose each $y_n$ lies in [`ModularCurve.normFreePartAt M q`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29), the range of the endomorphism `normFreeEnd M (normFreeRepsAt M q)`. Give $\mathrm{JOne}(M)$ the `HeckeAlgOne = MvPolynomial (Primes ⊕ ℕ) ℤ`-module structure `heckeModuleOneBar M`, and let `rep` denote the induced termwise actions of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and of `HeckeAlgOne` on the Tate module, a module over $\mathbb{Z}_p$. Writing $w$ for the Tate-module element `diamondGen u` $\cdot(\sigma\cdot y)-y$, where `diamondGen u` $=X_{\mathrm{inr}(u)}$, the conclusion is $$\tau\cdot\bigl(\mathrm{heckeGenOne}\,\langle q,hq\rangle\cdot w\bigr)-q\,w=0,$$ with `heckeGenOne ⟨q, hq⟩` $=X_{\mathrm{inl}(q)}$ and $q$ acting through its image in $\mathbb{Z}_p$.
--
--   This is the Frobenius half of the local analysis at a prime $q$ exactly dividing the level: on the norm-free part of the $p$-adic Tate module of $J_1(M)$, the element cut out by the diamond-twisted inertia operator $\langle u\rangle\sigma-1$ satisfies the relation $\tau T_q=q$, as in the Deligne–Rapoport description of the reduction of $X_1(M)$ at $q$ together with the Eichler–Shimura relation. It is used, alongside the companion inertia statement, by [`ModularCurve.exists_galoisRepAdic_charpoly_frobenius_and_inertia_mul_eq_zero_and_hecke_frobenius_mul_inertia_eq_zero_of_heckeDiamondChar_of_dvd_of_not_sq_dvd_of_le_div`](thm.html#ModularCurve.exists_galoisRepAdic_charpoly_frobenius_and_inertia_mul_eq_zero_and_hecke_frobenius_mul_inertia_eq_zero_of_heckeDiamondChar_of_dvd_of_not_sq_dvd_of_le_div) in producing the $p$-adic Galois representation with the required Frobenius and inertia relations at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rep_frobenius_rep_heckeGenOne_sub_smul_rep_diamondGen_rep_inertia_sub_eq_zero_normFreePartAt_tateModule_jOne_of_le_div.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.rep_frobenius_rep_heckeGenOne_sub_smul_rep_diamondGen_rep_inertia_sub_eq_zero_normFreePartAt_tateModule_jOne_of_le_div
    (M q p : ℕ) [NeZero M] [Fact p.Prime] (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M) (hMq : 5 ≤ M / q) (hpq : p ≠ q)
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : P.IsFrobeniusAt τ q)
    (u : ℕ) (hu : u ≡ 1 [MOD M / q])
    (hcyc : ∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ u)
    (y : TateModule p (ModularCurve.JOne M))
    (hy : ∀ n : ℕ, (y : ℕ → ModularCurve.JOne M) n ∈ ModularCurve.normFreePartAt M q) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ
        (TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne (ModularCurve.heckeGenOne ⟨q, hq⟩)
          (TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne (ModularCurve.diamondGen u)
            (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y) - y))
      - (q : ℤ_[p]) • (TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne (ModularCurve.diamondGen u)
            (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y) - y) = 0 := by sorry
