-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm
-- name    : ModularCurve.FullLevel.tateGal_mul_tateGL2_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/ae3f3742-8e52-58da-8647-10c36313329d
-- title:
--   Galois and GL₂(ℤ/q) actions commute on the Tate module
-- statement:
--   Fix a prime $q$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\lambda$. Consider the $\lambda$-adic Tate module $\mathrm{TateModule}\ \lambda\ (\mathrm{Jac}\ q\ M')$, the additive subgroup of sequences $x \colon \mathbb{N} \to \mathrm{Jac}\ q\ M'$ satisfying $\lambda^n \cdot x_n = 0$ and $\lambda \cdot x_{n+1} = x_n$ for all $n$, viewed as a $\mathbb{Z}_\lambda$-module. Two monoid homomorphisms into $\mathrm{End}_{\mathbb{Z}_\lambda}$ of this module are in play, both obtained by transporting additive endomorphisms of $\mathrm{Jac}\ q\ M'$ along `tateEnd` (the ring homomorphism induced by [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174)): first, `tateGal q M' lam`, which sends a $\mathbb{Q}$-algebra automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to the endomorphism of $\mathrm{Jac}\ q\ M'$ whose value at $x$ has component $\sigma \bullet x.\mathrm{eval}(\sigma^{-1} \bullet \zeta)$ at $\zeta$; second, `tateGL2 q M' lam`, coming from `gl2Jac q M'`, which is a chosen witness to the predicate `GL2Laws q M'` if that predicate holds and the trivial homomorphism otherwise, defined on $\mathrm{GL}_2(\mathbb{Z}/q)$ (the general linear group of $2 \times 2$ matrices over $\mathbb{Z}/q$). The assertion is that for every such $\sigma$ and every $x \in \mathrm{GL}_2(\mathbb{Z}/q)$ the two resulting $\mathbb{Z}_\lambda$-linear endomorphisms commute, i.e. $\mathrm{tateGal}(\sigma)\,\mathrm{tateGL2}(x) = \mathrm{tateGL2}(x)\,\mathrm{tateGal}(\sigma)$ as products (composites) in the endomorphism ring.
--
--   This records the classical fact that the $\mathrm{GL}_2(\mathbb{Z}/q)$-action on the modular curve of full level $q$ over $\Gamma_0(M')$ is given by correspondences defined over $\mathbb{Q}$, so that it commutes with the Galois action on the $\lambda$-adic Tate module of the Jacobian. It is one of the compatibility conditions verified when assembling the full-level Tate-module datum used in the construction of eigenspaces and Drinfeld-type specialisations, and is invoked by the statements producing such data and by the comparison of Tate modules with semistable models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.tateGal_mul_tateGL2_comm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime] :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : CuspidalType.GL2 q),
      ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateGL2 q M' lam x =
        ModularCurve.FullLevel.tateGL2 q M' lam x * ModularCurve.FullLevel.tateGal q M' lam σ := by sorry
