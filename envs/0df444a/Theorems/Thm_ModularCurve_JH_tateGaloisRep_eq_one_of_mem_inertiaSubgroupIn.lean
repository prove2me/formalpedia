-- Prove2me | Theorems.Thm_ModularCurve_JH_tateGaloisRep_eq_one_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.JH.tateGaloisRep_eq_one_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/a02fab0d-1eaf-5dcf-9d32-2386b9f497dc
-- title:
--   Inertia away from Mp acts trivially on TₚJ_H
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime, and $H$ a subgroup of $(\mathbb{Z}/M\mathbb{Z})^{\times}$; let $\ell$ be a prime with $\ell \nmid M$ and $\ell \neq p$. The assertion is that for every valuation subring $P$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `P.LiesOverPrime ℓ`, i.e. such that the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $P$, and for every $\sigma$ in `P.inertiaSubgroupIn ℚ` — the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained as the image of the inertia subgroup of $P$ inside the decomposition subgroup of $P$ under the inclusion of that decomposition subgroup — the endomorphism [`ModularCurve.JH.tateGaloisRep M H p σ`](def/ModularCurve_XH.html#L154) is the identity. Here [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15) is the additive subgroup of sequences $x \colon \mathbb{N} \to J_H(M)$ with $p^n\cdot x_n = 0$ and $p\cdot x_{n+1} = x_n$ for all $n$, a module over $\mathbb{Z}_p$, and `tateGaloisRep M H p` is the monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to its $\mathbb{Z}_p$-linear endomorphisms given by applying $\sigma$ to each component $x_n$.
--
--   This is the unramifiedness statement for the $p$-adic Tate module of the Jacobian $J_H(M)$ at primes $\ell$ not dividing $Mp$, in the style of the criterion of Néron–Ogg–Shafarevich: the Galois representation on $T_pJ_H(M)$ is trivial on inertia at every such place of $\overline{\mathbb{Q}}$. It is used, alongside the Eichler–Shimura relation, to control the ramification of the two-dimensional representations attached to Hecke eigenforms, and is specialised to full level in [`ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn`](thm.html#ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_tateGaloisRep_eq_one_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.JH.tateGaloisRep_eq_one_of_mem_inertiaSubgroupIn (M p : ℕ) [NeZero M]
    [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ = 1 := by sorry
