-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient
-- name    : HeckeEis.isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/be76747c-a24b-556c-a188-fe77396d204f
-- title:
--   Eisenstein alternative for eigensystems on a Steinberg quotient
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$ with $q \nmid N$, a set $S_0 \subseteq \mathbb{N}$, and a field $\kappa$ in which $6 \neq 0$ and $q + 1 = 0$. Let $V$ be a finite-dimensional $\kappa$-vector space carrying a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$, and let $\pi$ be a $\kappa$-linear map from the submodule $\ker(\mathrm{coeffSum})$ of the permutation module $\kappa[\mathbb{P}^1(\mathbb{Z}/q)] = (\mathrm{ProjLine}\ q \to_0 \kappa)$ — the kernel of the sum-of-coefficients functional, i.e. [`CuspidalType.steinberg`](def/CuspidalType_IsCuspidalOfType.html#L57) — to $V$, such that $\pi$ intertwines the permutation action [`CuspidalType.ind`](def/CuspidalType_IsCuspidalOfType.html#L51) with $\rho$, is surjective, and has kernel exactly the line spanned by the constant function $\mathbf{1}$ (`constFun`): $\pi v = 0$ iff $v = c \cdot \mathbf{1}$ for some $c \in \kappa$. Let $\mathrm{lam} : \mathbb{N} \to \kappa$. Assume the eigensystem predicate [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for $N$, the representation of $\Gamma_0(N)$ obtained by restricting $\rho$ along $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/q) \to \mathrm{GL}_2(\mathbb{Z}/q)$, the coefficient operators $\ell \mapsto \rho(\mathrm{diag}(\ell,1))$ when $\ell \not\equiv 0 \bmod q$ and the identity otherwise, the exceptional set $\{q\} \cup S_0$ and eigenvalues $\mathrm{lam}$; that is, there is a nonzero class $x$ in `coeffH1` of that representation which, for every prime $\ell \nmid N$ outside $\{q\} \cup S_0$, is an eigenvector with eigenvalue $\mathrm{lam}\ \ell$ for some operator satisfying `IsCoeffHeckeOnH1` at $\ell$. The conclusion is a disjunction: either the same eigensystem predicate holds for $N$ with the full permutation representation [`CuspidalType.ind`](def/CuspidalType_IsCuspidalOfType.html#L51) restricted along the same reduction map, with coefficient operators $\ell \mapsto \mathrm{ind}(\mathrm{diag}(\ell,1))$ (identity when $q \mid \ell$), the same exceptional set and the same $\mathrm{lam}$; or $\mathrm{lam}\ \ell = \ell + 1$ in $\kappa$ for every prime $\ell \nmid N$ with $\ell \notin \{q\} \cup S_0$.
--
--   This is the dévissage step along $0 \subset \kappa\cdot\mathbf{1} \subset \mathrm{St} \subset \kappa[\mathbb{P}^1(\mathbb{F}_q)]$ in cohomological form: an eigensystem occurring in $H^1(\Gamma_0(N), -)$ with coefficients in the quotient of the Steinberg module by the constants is propagated to the full permutation module, the only alternative being the Eisenstein system $\lambda_\ell = \ell + 1$. It is used in the level-changing argument at the prime $q$ for the representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (κ : Type) [Field κ] (h6 : (6 : κ) ≠ 0) (hq1 : (q : κ) + 1 = 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ)
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
