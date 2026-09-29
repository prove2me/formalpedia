-- Prove2me | Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jOne
-- name    : ModularCurve.frobeniusQuadratic_tateModule_jOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/481b33d8-a5e8-5516-8ddb-c23870928106
-- title:
--   Eichler–Shimura relation on the Tate module of J₁(M)
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime. Write $J_1(M)$ for [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb Q}$ of the Laurent-series function field of $X_1(M)$. Assume [`ModularCurve.HeckeDiamondCommuteBar M`](def/ModularCurve_X1HeckeModule.html#L54): the $\mathbb Z$-endomorphisms of $J_1(M)$ given by [`ModularCurve.heckeOperatorOneBar M`](def/ModularCurve_X1HeckeModule.html#L36) at primes and by [`ModularCurve.diamondOneBar M`](def/ModularCurve_X1Diamond.html#L98) at natural numbers commute pairwise, so that the polynomial ring $\mathrm{HeckeAlgOne}=\mathbb Z[X_i : i \in \mathrm{Primes}\sqcup\mathbb N]$ acts on $J_1(M)$ through [`ModularCurve.heckeModuleOneBar M`](def/ModularCurve_X1HeckeModule.html#L129), the generator $X_{\mathrm{inl}\,\ell}$ acting as the $\ell$-th Hecke operator and $X_{\mathrm{inr}\,d}$ as the $d$-th diamond operator. Let $\ell$ be a prime with $\ell \nmid Mp$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $y \mapsto y^{\ell}$. Then for every $x$ in the $p$-adic Tate module of $J_1(M)$ — a sequence $(x_n)$ with $p^n x_n = 0$ and $p\,x_{n+1}=x_n$ — the induced actions on the Tate module satisfy $\langle \ell\rangle \sigma^2 x - T_\ell\,\sigma x + \ell\, x = 0$.
--
--   This is the Eichler–Shimura congruence relation, in the form of a quadratic relation satisfied by an arithmetic Frobenius at a prime $\ell$ of good reduction acting on the $p$-adic Tate module of the Jacobian of $X_1(M)$, here on the $q$-expansion model of the curve. It is the input from which the Galois representations attached to Hecke eigenclasses are obtained together with the characteristic polynomial of Frobenius, in the statements [`ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar`](thm.html#ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar) and its variants with inertia conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobeniusQuadratic_tateModule_jOne.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.frobeniusQuadratic_tateModule_jOne (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (x : TateModule p (ModularCurve.JOne M)) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne (ModularCurve.diamondGen ℓ)
        (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
          (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
      - TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne
          (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)
          (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
      + ℓ • x = 0 := by sorry
