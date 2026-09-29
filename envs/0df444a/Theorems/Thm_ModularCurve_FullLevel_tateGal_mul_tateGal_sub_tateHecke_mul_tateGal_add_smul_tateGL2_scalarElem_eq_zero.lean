-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero
-- name    : ModularCurve.FullLevel.tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/6097488d-c1a7-594d-9b08-ae8cda1fc3e8
-- title:
--   Eichler–Shimura relation with scalar diamond at full level q
-- statement:
--   Let $q$ and $\lambda$ be primes and $M'$ a nonzero natural number, and suppose the predicate `GL2Laws q M'` holds, i.e. there is a monoid homomorphism $G$ from $\mathrm{GL}_2(\mathbb{Z}/q)$ to the additive endomorphisms of the abelian group `Jac q M'` such that $G$ sends the reduction mod $q$ of every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ to `slJac q M' γ` (the reindexing of `Jac` by the level operation of $\gamma^{-1}$) and sends $\mathrm{diag}(1,d)$, for $d \in (\mathbb{Z}/q)^\times$, to `diagJac q M' d`. Let $\ell$ be a prime coprime to $q$, not dividing $M'$ and distinct from $\lambda$; let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $P$, and let $\sigma$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ which is a Frobenius at $\ell$ for $P$, meaning $\sigma$ lies in the decomposition subgroup of $P$ over $\mathbb{Q}$ and acts on the residue field of $P$ by $x \mapsto x^{\ell}$. Then, in the ring of $\mathbb{Z}_\lambda$-linear endomorphisms of the $\lambda$-adic Tate module $T_\lambda(\mathrm{Jac}\, q\, M')$ (the sequences $(x_n)$ with $\lambda^n x_n = 0$ and $\lambda x_{n+1} = x_n$), one has $$\rho(\sigma)^2 - T_\ell\,\rho(\sigma) + \ell \cdot G(\ell \cdot 1) = 0,$$ where $\rho =$ `tateGal q M' lam` is the Galois action induced by `galJac`, $T_\ell$ is the image under `tateHecke q M' lam` of the Hecke generator `heckeGen ⟨ℓ, hℓ⟩`, and $G(\ell\cdot 1)$ is the image under `tateGL2 q M' lam` of the scalar matrix [`CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hℓq)`](def/CuspidalType_IsCuspidalOfType.html#L32), the coefficient $\ell$ being taken in $\mathbb{Z}_\lambda$.
--
--   This is the Eichler–Shimura congruence relation for the modular curve of full level $q$ over $\Gamma_0(M')$, in the shape where the diamond operator at $\ell$ is expressed as the action of the scalar matrix $\ell \cdot 1$ of $\mathrm{GL}_2(\mathbb{Z}/q)$. It is used in the construction of Tate-module data of full level $q$, in the two `FullLevelTate` existence statements about eigenspace homomorphisms and Drinfeld specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve.FullLevel
open ModularCurve

theorem ModularCurve.FullLevel.tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]
    (hG : ModularCurve.FullLevel.GL2Laws q M')
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ.Coprime q) (hℓM' : ¬ ℓ ∣ M') (hℓlam : ℓ ≠ lam)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ ℓ) :
    ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateGal q M' lam σ
      - ModularCurve.FullLevel.tateHecke q M' lam (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)
          * ModularCurve.FullLevel.tateGal q M' lam σ
      + (ℓ : ℤ_[lam]) • ModularCurve.FullLevel.tateGL2 q M' lam
          (CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hℓq)) = 0 := by sorry
