-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt
-- name    : MvFormalGroup.BigWittLaw.exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/9bb39efc-acfd-547c-938c-a26b286e6efa
-- title:
--   Cartier splitting of the big Witt law over a ℤₚ-algebra
-- statement:
--   Let $p$ be a prime and let $R$ be a commutative ring equipped with an algebra structure over the $p$-adic integers $\mathbb{Z}_p$. The assertion is the existence of a doubly indexed family $\pi : \mathbb{N} \to \mathbb{N} \to \mathrm{MvPowerSeries}\ \mathbb{N}\ R$ with two properties. First, for every $n$ with $0 < n$ and $p \nmid n$: the family $k \mapsto \pi\,n\,k$ satisfies `MvPowerSeries.HasSubst`, every $\pi\,n\,k$ has zero constant coefficient, and for every $k$, substituting the big Witt addition family [`MvFormalGroup.BigWittLaw.addFam R`](def/MvFormalGroup_BigWittLaw.html#L67) (whose $m$-th member is the image in $R$ of $X_{(0,m)} + X_{(1,m)} + \sum_{i<m} X_{(0,i)}X_{(1,m-1-i)}$) into $\pi\,n\,k$ gives the same result as substituting the pair family [`MvFormalGroup.WittLaw.pairFam (π n)`](def/MvFormalGroup_CartierModule.html#L341), which sends a variable $(i,m)$ to $\pi\,n\,m$ written in the $i$-th block of variables, into the $k$-th $p$-typical Witt addition series [`MvFormalGroup.WittLaw.addFam p R k`](def/MvFormalGroup_CartierModule.html#L107) (the image of `WittVector.wittAdd p k`); that is, each $\pi\,n$ is a homomorphism from the big Witt group law to the $p$-typical one. Second, for every $N : \mathbb{N}$, the truncation in degrees $< N$ of the one-variable series over $\mathrm{MvPowerSeries}\ \mathbb{N}\ R$ with coefficient $1$ in degree $0$ and coefficient $X_{k-1}$ in degree $k \ge 1$, namely $1 + \sum_{k \ge 0} a_k t^{k+1}$, agrees with the truncation in degrees $< N$ of the finite product, over those $n \in \{0,\dots,N-1\}$ with $0 < n$ and $p \nmid n$, of the series whose degree-$0$ coefficient is $1$, whose degree-$k$ coefficient for $n \mid k$, $k>0$, is the result of substituting $\pi\,n$ into the image under $\mathbb{Z}_p \to R$ of the Artin–Hasse coordinate polynomial [`MvFormalGroup.ArtinHasse.coord p (k/n - 1)`](def/MvFormalGroup_ArtinHasse.html#L103) (the coefficient of $t^{k/n}$ in $\prod_{m < k/n}$ `scaled p (p^m) (X m)`), and whose remaining coefficients vanish.
--
--   This is Cartier's first theorem on $p$-typification in the form of a splitting of the big Witt (Lambda) formal group over a $\mathbb{Z}_p$-algebra into copies of the $p$-typical Witt group law, one for each $n$ prime to $p$, the $n$-th factor being congruent to $1$ modulo $t^n$ so that the product identity is stated for each truncation. It is used by [`MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt) in the passage from curves on a formal group to $p$-typical curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] :
    ∃ π : ℕ → ℕ → MvPowerSeries ℕ R,
      (∀ n, 0 < n → ¬ p ∣ n →
        MvPowerSeries.HasSubst (π n) ∧ (∀ k, MvPowerSeries.constantCoeff (π n k) = 0) ∧
        ∀ k, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (π n k) =
          MvPowerSeries.subst (MvFormalGroup.WittLaw.pairFam (π n)) (MvFormalGroup.WittLaw.addFam p R k)) ∧
      ∀ N : ℕ,
        PowerSeries.trunc N
            (PowerSeries.mk fun k => if k = 0 then (1 : MvPowerSeries ℕ R) else MvPowerSeries.X (k - 1)) =
          PowerSeries.trunc N
            (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n),
              PowerSeries.mk fun k =>
                if k = 0 then (1 : MvPowerSeries ℕ R)
                else if n ∣ k then
                  MvPowerSeries.subst (π n)
                    (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p (k / n - 1))) :
                      MvPowerSeries ℕ R)
                else 0) := by sorry
