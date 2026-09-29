-- Prove2me | Theorems.Thm_HeckeEis_modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero
-- name    : HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/3ce7775a-44a4-5cf9-9850-a36c19c7d0cb
-- title:
--   Injectivity of Eichler–Shimura on Mₙ₊₂(Γ₀(N))
-- statement:
--   Let $N \ge 1$ and $n \ge 0$ be natural numbers, let $f$ be a modular form of weight $(n:\mathbb Z)+2$ for $\Gamma_0(N)$, and let $F \colon \mathfrak H \to \mathrm{BinaryForm}\,\mathbb C\,n$ take values in the submodule of binary forms in $\mathbb C[X_0,X_1]$ homogeneous of degree $n$. Write $\rho$ for the composite of [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61), the representation of $\mathrm{SL}_2(\mathbb Z)$ on binary forms of degree $n$ given by the substitution $X_j \mapsto \sum_i M_{ij} X_i$, with the inclusion of $\Gamma_0(N)$. Assume: (i) $F$ is an Eichler integral of $f$, i.e. for every multidegree $d$ and every $\tau \in \mathfrak H$ the function $z \mapsto \mathrm{coeff}_d\bigl(F(z)\bigr)$ has derivative $f(\tau)\,\mathrm{coeff}_d\bigl((\tau X_0 + X_1)^n\bigr)$ at $\tau$; (ii) $F$ is an equivariant primitive for $\rho$, i.e. for every $\gamma \in \Gamma_0(N)$ the function $\tau \mapsto F(\gamma \cdot \tau) - \rho(\gamma)F(\tau)$ is constant on $\mathfrak H$; (iii) the associated inhomogeneous cocycle $z(\gamma) = F(\gamma \cdot i) - \rho(\gamma)F(i)$, which satisfies $z(\gamma\delta) = z(\gamma) + \rho(\gamma)z(\delta)$, has vanishing image under [`HeckeEis.coeffH1Mk`](def/Gamma0CoeffCohomologyEigen.html#L27), that is, its class in $\mathrm{coeffCocycles}\,\rho$ modulo the coboundaries (the range of the coboundary map for $\rho$) is zero. Then $f = 0$.
--
--   This is the injectivity of the Eichler–Shimura period map on the whole space $M_{n+2}(\Gamma_0(N))$, with no parabolic condition imposed on the cohomology, so that Eisenstein series are included as well as cusp forms. It is used to pass from a modular form that is an eigenvector for the Hecke action to an eigensystem in the coefficient cohomology $H^1(\Gamma_0(N), \mathrm{Sym}^n)$, as in [`HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul`](thm.html#HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul) and [`ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen`](thm.html#ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero (N : ℕ) [NeZero N] (n : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (h0 : HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      ⟨hF.cocycle, hF.cocycle_mem_coeffCocycles⟩ = 0) :
    f = 0 := by sorry
