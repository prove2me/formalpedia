-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three
-- name    : HeckeEis.isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/626af064-072f-5755-a336-053ea27b56a9
-- title:
--   Characteristic 3: eigensystems lift from the Steinberg quotient or are Eisenstein
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q\nmid N$, let $S_0$ be a finite set of naturals, and let $\kappa$ be a field of characteristic $3$ in which $q+1=0$. Let $V$ be a finite-dimensional $\kappa$-vector space carrying a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$, and let $\pi$ be a $\kappa$-linear map from [`CuspidalType.steinberg q κ`](def/CuspidalType_IsCuspidalOfType.html#L57), the kernel of the coefficient-sum map on $\kappa[\mathbb{P}^1(\mathbb{Z}/q)]$, to $V$ which is equivariant for the permutation action on $\mathbb{P}^1(\mathbb{Z}/q)$, surjective, and whose kernel consists exactly of the scalar multiples of the constant function; thus $V$ realises the Steinberg representation modulo constants. Let $\lambda:\mathbb{N}\to\kappa$ and $n:\mathbb{N}\to\mathbb{Z}$ satisfy $\lambda_\ell=n_\ell$ in $\kappa$ for all primes $\ell\nmid N$ outside $\{q\}\cup S_0$. Let $k$ be a field of characteristic $3$ and $\bar\rho$ a residual Galois representation over $k$: a two-dimensional $k$-space with a multiplicative action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ factoring through a finite level. Assume $\bar\rho$ is absolutely irreducible (its base change to $\overline{k}$ is irreducible) and, more strongly, that for every field $K$ that is a $k$-algebra and every subgroup $G$ of index $2$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, the only $G$-stable $K$-submodules of $(\bar\rho\otimes_k K).V$ are $\bot$ and $\top$. Assume further that for every prime $\ell\nmid N$ with $\ell\notin\{q\}\cup S_0$ and $\ell\ne 3$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ that is a Frobenius at $\ell$ for $A$ (lying in the decomposition subgroup and acting as $x\mapsto x^{\ell}$ on the residue field), one has $\mathrm{tr}\,\bar\rho(\sigma)=n_\ell$ in $k$. Finally assume that $\lambda$ occurs as an $H^1$-eigensystem of level $N$ away from $\{q\}\cup S_0$ for the coefficient system obtained by composing $\rho$ with $\Gamma_0(N)\hookrightarrow \mathrm{SL}_2(\mathbb{Z})\to\mathrm{SL}_2(\mathbb{Z}/q)\to\mathrm{GL}_2(\mathbb{Z}/q)$, the operator at $\ell$ being $\rho(\mathrm{diag}(\ell,1))$ when $\ell\not\equiv 0 \bmod q$ and the identity otherwise; that is, some nonzero class in the corresponding $H^1$ is, for each such $\ell$, an eigenvector with eigenvalue $\lambda_\ell$ for some operator satisfying the Hecke relation at $\ell$. Then either the same eigensystem condition holds with the full induced representation $\kappa[\mathbb{P}^1(\mathbb{Z}/q)]$ in place of $V$ (with the operator at $\ell$ given by the action of $\mathrm{diag}(\ell,1)$ on $\kappa[\mathbb{P}^1(\mathbb{Z}/q)]$, or the identity when $q\mid\ell$), or $\lambda_\ell=\ell+1$ for all primes $\ell\nmid N$ outside $\{q\}\cup S_0$.
--
--   This is the characteristic-$3$ case of the dévissage that pulls an eigensystem back along the surjection of the Steinberg representation onto its quotient by the constants: the obstruction lies in $H^2(\Gamma_0(N),\kappa)$, which at $p=3$ is controlled by the hypothesis that $\bar\rho$ remains irreducible on every index-two subgroup (ruling out systems induced from $\mathbb{Q}(\sqrt{-3})$), leaving either a lift to the induced representation or an Eisenstein eigensystem $\lambda_\ell=\ell+1$. It is used in the construction of a non-Eisenstein parabolic $H^1$ class of lowered level for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ) (hS₀ : S₀.Finite)
    (κ : Type) [Field κ] [CharP κ 3] (hq1 : (q : κ) + 1 = 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ) (n : ℕ → ℤ) (hlam : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (n ℓ : κ))
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → ℓ ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    HeckeEis.IsEigensystemH1 N ((CuspidalType.ind q κ).comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then (CuspidalType.ind q κ) (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))
        else LinearMap.id) (insert q S₀) lam ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by sorry
