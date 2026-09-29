-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
-- name    : HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/f6eb7f21-31ed-5f02-b996-3897e5da8fc6
-- title:
--   Eichler–Shimura mod p: eigensystems occur in H¹(Γ₀(N),Symⁿ)
-- statement:
--   Let $p$ be a prime, $N\ge 1$, let $S\subseteq\mathbb{N}$ be a set of naturals, let $n\in\mathbb{N}$ and $k\in\mathbb{Z}$ with $k=n+2$, and let $f$ be a nonzero modular form of weight $k$ on $\Gamma_0(N)$. Let $a\colon\mathbb{N}\to\overline{\mathbb{Z}}$ take values in the integral closure of $\mathbb{Z}$ in $\mathbb{C}$, and assume that for every prime $\ell$ with $\ell\nmid N$ and $\ell\notin S$ one has [`ModularForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L20) applied to $f$ equal to $a_\ell\cdot f$, where this operator is the endomorphism of weight-$k$ forms on $\Gamma_0(N)$ induced by $g\mapsto$ `heckeU` $+\;g\mid[k]$ `heckeDiagMatrix` at $\ell$. Let $\kappa$ be a field of characteristic $p$ and $\varphi\colon\overline{\mathbb{Z}}\to\kappa$ a ring homomorphism. Consider the representation of $\Gamma_0(N)$ obtained by restricting the action of $\mathrm{SL}_2(\mathbb{Z})$ on the degree-$n$ homogeneous part of $\kappa[X_0,X_1]$ by substitution $X_j\mapsto\sum_i M_{ij}X_i$, and for each $\ell$ the coefficient map given by substitution along $\mathrm{diag}(\ell,1)$. The conclusion is that there is a nonzero class $x$ in $H^1$ (cocycles modulo coboundaries for this representation) such that for every prime $\ell\nmid N$ with $\ell\notin S$ there is a $\kappa$-linear endomorphism $T$ of $H^1$ realising, on each cocycle $z$, the function `coeffHeckeFun` at $\ell$ for that coefficient map (itself again a cocycle, representing $T[z]$), and $Tx=\varphi(a_\ell)\,x$.
--
--   This is the mod $p$ Eichler–Shimura statement in the form used by Ash–Stevens: the system of Hecke eigenvalues of an analytically given eigenform of weight $n+2$ on $\Gamma_0(N)$, reduced through $\varphi$, occurs in the first cohomology of $\Gamma_0(N)$ with coefficients in binary forms of degree $n$ over $\kappa$, with no restriction on $p$, $N$ or the weight. It is the input for attaching a Galois representation to the reduced eigensystem, and is cited in [`GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le`](thm.html#GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ) (n : ℕ) (k : ℤ) (hk : (n : ℤ) + 2 = k)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0)
    (a : ℕ → integralClosure ℤ ℂ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      ModularForm.heckeTLin k hℓ hℓN f = ((a ℓ : integralClosure ℤ ℂ) : ℂ) • f)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) :
    HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S (fun ℓ => φ (a ℓ)) := by sorry
