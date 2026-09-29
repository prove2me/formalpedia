-- Prove2me | Theorems.Thm_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
-- name    : HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/594ed108-8be3-5053-a989-40ddb3a77056
-- title:
--   Boundary Hecke eigensystems arise from modular forms
-- statement:
--   Fix $N\ge 1$ and $n\ge 0$, an arbitrary set $S_0\subseteq\mathbb{N}$ of excluded primes, and a function $\Lambda\colon\mathbb{N}\to\mathbb{C}$. Let $\rho$ be the representation of $\Gamma_0(N)$ obtained by restricting along $\Gamma_0(N)\hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ the action [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61) of $\mathrm{SL}(2,\mathbb{Z})$ on the space of homogeneous polynomials of degree $n$ in $\mathbb{C}[X_0,X_1]$ given by the substitution $X_j\mapsto\sum_i M_{ij}X_i$. Write $H^1=$ [`HeckeEis.coeffH1`](def/Gamma0CoeffCohomologyEigen.html#L16) $\rho$ for the quotient of the module of inhomogeneous $1$-cocycles $z(gh)=z(g)+\rho(g)z(h)$ by the coboundaries, and let [`HeckeEis.coeffH1parToH1`](def/Gamma0CoeffCohomologyEigen.html#L43) be the induced map to $H^1$ from the analogous quotient `coeffH1par` formed from the parabolic cocycles. Let $x\in H^1$ be a class not lying in the image of that map. Assume that for every prime $\ell$ with $\ell\nmid N$ and $\ell\notin S_0$ there is a $\mathbb{C}$-linear endomorphism $T$ of $H^1$ which is a Hecke operator at $\ell$ in the sense of [`HeckeEis.IsCoeffHeckeOnH1`](def/Gamma0CoeffCohomologyEigen.html#L61) with coefficient map [`HeckeEis.binaryFormAlphaAdj`](def/HeckeEis_BinaryFormRep.html#L82) $\mathbb{C}\,n\,\ell$ (that is, for each cocycle $z$ there is a cocycle $w$ whose underlying function is [`HeckeEis.coeffHeckeFun`](def/Gamma0CoeffCohomology.html#L129) $N\,\ell\,\rho$ applied to $z$, with $T[z]=[w]$), such that $Tx-\Lambda(\ell)\,x$ lies in the image of `coeffH1parToH1`. The conclusion is that there exists a nonzero modular form $f$ of weight $(n:\mathbb{Z})+2$ on $\Gamma_0(N)$ with [`ModularForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L20) $((n:\mathbb{Z})+2)$ applied to $f$ equal to $\Lambda(\ell)\,f$ for every prime $\ell\nmid N$ with $\ell\notin S_0$.
--
--   This is the Eisenstein, or boundary, half of the Eichler–Shimura correspondence in the form needed here: a system of Hecke eigenvalues occurring in the quotient of the full group cohomology $H^1(\Gamma_0(N),\mathrm{Sym}^n)$ by the parabolic part is realised by a nonzero, not necessarily cuspidal, modular form of weight $n+2$ on $\Gamma_0(N)$. It is used by [`HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1`](thm.html#HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1), which packages the eigenvector hypothesis into an eigensystem statement on $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
    (N : ℕ) [NeZero N] (n : ℕ) (S₀ : Set ℕ) (Λ : ℕ → ℂ)
    (x : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : x ∉ LinearMap.range (HeckeEis.coeffH1parToH1
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∃ T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          →ₗ[ℂ] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         HeckeEis.IsCoeffHeckeOnH1 N ℓ
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) T) ∧
        T x - Λ ℓ • x ∈ LinearMap.range (HeckeEis.coeffH1parToH1
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), f ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f := by sorry
