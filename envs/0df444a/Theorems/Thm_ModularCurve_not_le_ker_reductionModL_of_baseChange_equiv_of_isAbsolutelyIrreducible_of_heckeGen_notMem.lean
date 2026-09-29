-- Prove2me | Theorems.Thm_ModularCurve_not_le_ker_reductionModL_of_baseChange_equiv_of_isAbsolutelyIrreducible_of_heckeGen_notMem
-- name    : ModularCurve.not_le_ker_reductionModL_of_baseChange_equiv_of_isAbsolutelyIrreducible_of_heckeGen_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/bb55c544-addc-562c-828d-8535b00d8fa5
-- title:
--   Copies of ρ̄ in J₀(M)[𝔪] are not killed mod p
-- statement:
--   Fix $M\ge 1$ and a prime $p$ with $p\neq 2$ and $p\nmid M$. Let $\mathfrak m$ be a maximal ideal of `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$ containing $p$ and not containing the variable $X_p$, let $k$ be a field and $\iota:\mathtt{HeckeAlg}/\mathfrak m\to k$ a ring homomorphism. Let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $2$-dimensional $k$-space with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to its endomorphisms which is trivial on the automorphisms fixing some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$; assume $\bar\rho$ is absolutely irreducible, i.e. its base change to $\overline{k}$ has no stable subspace other than $\bot$ and $\top$. Assume, for a finite set $S_0$ of naturals, that for every prime $\ell\notin S_0$ with $\ell\nmid M$, $\ell\neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ and every $\sigma$ in the decomposition group of $A$ acting as $x\mapsto x^{\ell}$ on the residue field, $\mathrm{tr}\,\rho(\sigma)=\iota(X_\ell\bmod\mathfrak m)$. Give $J_0(M)=\mathrm{Pic}^0$ of the level-$M$ modular function field over $\overline{\mathbb Q}$ its `heckeModuleBar` Hecke-module structure and assume the Galois and Hecke actions commute. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $p$ is a non-unit, let $K$ be the $\mathtt{HeckeAlg}/\mathfrak m$-submodule of the $\mathfrak m$-torsion of $J_0(M)$ consisting exactly of the elements whose reduction `reductionModL A M` vanishes, and let $V$ be a further such submodule equipped with a monoid homomorphism $\sigma V$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathtt{HeckeAlg}/\mathfrak m$-linear endomorphisms of $V$ agreeing with the Galois action `mTorsionGaloisRep` on the $\mathfrak m$-torsion, with $\dim_{\mathtt{HeckeAlg}/\mathfrak m}V=2$, and with a $k$-linear isomorphism $e:k\otimes_{\mathtt{HeckeAlg}/\mathfrak m}V\xrightarrow{\sim}\bar\rho.V$ (the $k$-algebra structure coming from $\iota$) intertwining $\sigma V$ with $\rho$. Then $V\not\le K$.
--
--   This is the statement that a copy of $\bar\rho$ inside $J_0(M)[\mathfrak m]$ at an ordinary, non-Eisenstein maximal ideal ($X_p\notin\mathfrak m$, $p$ odd, $p\nmid M$) is not of multiplicative type: it cannot reduce identically to zero at a place above $p$. It is used in the proof that the $\mathfrak m$-torsion of $J_0(M)$ has $\mathtt{HeckeAlg}/\mathfrak m$-dimension at most $2$ in this situation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_le_ker_reductionModL_of_baseChange_equiv_of_isAbsolutelyIrreducible_of_heckeGen_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.not_le_ker_reductionModL_of_baseChange_equiv_of_isAbsolutelyIrreducible_of_heckeGen_notMem
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hord : heckeGen ⟨p, Fact.out⟩ ∉ 𝔪)
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : letI := heckeModuleBar M; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪))
    (hK : letI := heckeModuleBar M
      ∀ w : ↥(heckeTorsion (JZero M) 𝔪), w ∈ K ↔ reductionModL A M (w : JZero M) = 0)
    (V : letI := heckeModuleBar M; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪))
    (σV : letI := heckeModuleBar M; haveI := hsmc
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (HeckeAlg ⧸ 𝔪) ↥V)
    (hσV : letI := heckeModuleBar M; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
        ((σV σ v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) =
          mTorsionGaloisRep (JZero M) 𝔪 σ (v : ↥(heckeTorsion (JZero M) 𝔪)))
    (hV2 : letI := heckeModuleBar M; Module.finrank (HeckeAlg ⧸ 𝔪) ↥V = 2)
    (e : letI := heckeModuleBar M; letI := ι.toAlgebra; TensorProduct (HeckeAlg ⧸ 𝔪) k ↥V ≃ₗ[k] ρbar.V)
    (he : letI := heckeModuleBar M; letI := ι.toAlgebra
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : k) (v : ↥V),
        e (c ⊗ₜ[HeckeAlg ⧸ 𝔪] σV σ v) = ρbar.ρ σ (e (c ⊗ₜ[HeckeAlg ⧸ 𝔪] v))) :
    letI := heckeModuleBar M
    ¬ V ≤ K := by sorry
