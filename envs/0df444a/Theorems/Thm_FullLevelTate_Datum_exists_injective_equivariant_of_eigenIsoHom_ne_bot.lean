-- Prove2me | Theorems.Thm_FullLevelTate_Datum_exists_injective_equivariant_of_eigenIsoHom_ne_bot
-- name    : FullLevelTate.Datum.exists_injective_equivariant_of_eigenIsoHom_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a38f9cba-119d-51fb-959e-de96a72508e7
-- title:
--   Embedding an adic representation into a nonzero Hecke eigenspace
-- statement:
--   Fix a prime $q$, a nonzero natural number $M'$ and a Noetherian local commutative ring $O'$, and let $D$ be a full-level Tate datum of level $(q,M')$ over $O'$: a finite free $O'$-module $D.V$ carrying an adically continuous action `gal` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as $\operatorname{Aut}$ on $\overline{\mathbb{Q}}$), an action `gl2` of $\mathrm{GL}_2(\mathbb{Z}/q)$ and an action `hecke` of the polynomial Hecke algebra $\mathbb{Z}[T_\ell]_{\ell\text{ prime}}$, the three pairwise commuting, with `gal` unramified at each prime $\ell\neq q$ with $\ell\nmid M'$ and $\ell$ a unit modulo the maximal ideal, and satisfying the Eichler–Shimura relation at Frobenius elements over such $\ell$. Let $K$ be a field of characteristic zero which is an $O'$-algebra with $O'\to K$ injective, let $\chi$ be a representation of a subgroup $H\le \mathrm{GL}_2(\mathbb{Z}/q)$ on a $K$-vector space $W$ such that for every $c\in(\mathbb{Z}/q)^\times$ the scalar matrix $cI$ lies in $H$ and acts trivially through $\chi$, and let $hk$ be a ring homomorphism from the Hecke algebra to $K$. Assume the eigenspace $D.\mathrm{eigenIsoHom}$ — the $K$-space of $K$-linear maps $f\colon W\to K\otimes_{O'}D.V$ with $f\circ\chi(h)=\mathrm{gl2}(h)_K\circ f$ for all $h\in H$ and $\mathrm{hecke}(t)_K\circ f=hk(t)\,f$ for all Hecke elements $t$ — is nonzero. Let $S$ be a finite set of naturals and $\rho$ an adic Galois representation over $O'$, that is, a finite free $O'$-module $\rho.V$ of rank $2$ with an adically continuous Galois action, such that: (i) for every prime $\ell\neq q$ with $\ell\nmid M'$, $\ell\notin S$ and $\ell$ outside the maximal ideal of $O'$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $\ell$ is a nonunit and every $s$ which lies in the decomposition group of $A$ and induces $x\mapsto x^{\ell}$ on its residue field, the characteristic polynomial of $\rho(s)$ maps to $X^2-hk(T_\ell)X+\ell$ in $K[X]$; (ii) every $K$-subspace of $K\otimes_{O'}\rho.V$ stable under all base-changed $\rho(s)$ is $\bot$ or $\top$; (iii) there is $c$ with $\rho(c)^2=1$ and $\det\rho(c)=-1$. Then there is an injective $K$-linear map $\varphi\colon K\otimes_{O'}\rho.V\to D.\mathrm{eigenIsoHom}$ with $\varphi\circ\rho(s)_K=\mathrm{eigenIsoHomGal}(s)\circ\varphi$ for every $s$, the latter action being post-composition with the base change of $\mathrm{gal}(s)$.
--
--   This is the comparison step identifying a two-dimensional irreducible odd adic Galois representation, whose Frobenius characteristic polynomials match the Hecke eigenvalues of a homomorphism $hk$, with a subrepresentation of the Galois representation on the corresponding $\chi$-isotypic Hecke eigenspace attached to a full-level Tate datum. It is used in the determination of the inertia labels of newforms whose associated representation is cuspidal of a prescribed type at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_Datum_exists_injective_equivariant_of_eigenIsoHom_ne_bot.lean

import Definitions.Def_FullLevelTate_IsoHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

theorem FullLevelTate.Datum.exists_injective_equivariant_of_eigenIsoHom_ne_bot
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (O' : Type) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O']
    (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [CharZero K] [Algebra O' K] (hOK : Function.Injective (algebraMap O' K))
    {H : Subgroup (CuspidalType.GL2 q)} {W : Type} [AddCommGroup W] [Module K W] (χ : Representation K H W)
    (hcentral : ∀ c : (ZMod q)ˣ, ∃ h : H, (h : CuspidalType.GL2 q) = CuspidalType.scalarElem q c ∧ χ h = 1)
    (hk : ModularCurve.HeckeAlg →+* K) (hne : D.eigenIsoHom K χ hk ≠ ⊥)
    (S : Finset ℕ) (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ¬ ℓ ∣ M' → ℓ ∉ (↑S : Set ℕ) →
      (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt s ℓ →
          (LinearMap.charpoly (ρ.ρ s)).map (algebraMap O' K) =
            X ^ 2 - C (hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) * X + C ((ℓ : K)))
    (hirr : ∀ U : Submodule K (K ⊗[O'] ρ.V),
      (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ v ∈ U, (ρ.ρ s).baseChange K v ∈ U) →
        U = ⊥ ∨ U = ⊤)
    (hodd : ∃ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρ.ρ c * ρ.ρ c = 1 ∧ LinearMap.det (ρ.ρ c) = -1) :
    ∃ φ : K ⊗[O'] ρ.V →ₗ[K] D.eigenIsoHom K χ hk,
      Function.Injective φ ∧
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          φ ∘ₗ (ρ.ρ s).baseChange K = D.eigenIsoHomGal K χ hk s ∘ₗ φ := by sorry
