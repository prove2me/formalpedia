-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_eigenform
-- name    : HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_eigenform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/03a3e443-64e7-56e7-a570-2258cff84066
-- title:
--   Integral parabolic mod-p eigenclass attached to a Hecke eigenform
-- statement:
--   Fix $N \ge 1$, $n \ge 0$, a set $S$ of naturals, a prime $p$, a predicate $Q$ on naturals and a function $a : \mathbb{N} \to \mathbb{Z}$. Let $\mathfrak{m}'$ be a prime ideal of the integral closure $\overline{\mathbb{Z}}$ of $\mathbb{Z}$ in $\mathbb{C}$ with $p \in \mathfrak{m}'$, let $\alpha : \mathbb{N} \to \overline{\mathbb{Z}}$, and let $f \ne 0$ be a cusp form of weight $n+2$ on $\Gamma_0(N)$ such that for every prime $\ell \notin S$ with $\ell \nmid N$ and $Q(\ell)$ one has [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) $(n+2)$ applied to $f$ equal to $\alpha_\ell \cdot f$ (the image of $\alpha_\ell$ in $\mathbb{C}$), and $\alpha_\ell - a(\ell) \in \mathfrak{m}'$ for all such $\ell$. Write $\rho$ for the representation of $\Gamma_0(N)$ on the degree-$n$ homogeneous part of $\mathbb{Z}[X_0,X_1]$ obtained by restricting [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61) (a matrix $M$ substitutes $X_j \mapsto \sum_i M_{ij} X_i$), and let [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho$ be the quotient of the module of parabolic cocycles (functions $z$ on $\Gamma_0(N)$ with $z(gh) = z(g) + \rho(g) z(h)$ and $z(\gamma) \in \operatorname{range}(\rho(\gamma) - 1)$ whenever $\operatorname{tr}(\gamma)^2 = 4$) by the coboundaries it contains. The assertion is that there is an element $y$ of this quotient which is not $p$ times any element, and such that for every prime $\ell \notin S$ with $\ell \nmid N$ and $Q(\ell)$, and every additive endomorphism $T$ of the quotient which is induced by the cochain-level operator [`HeckeEis.coeffHeckeFun`](def/Gamma0CoeffCohomology.html#L129) $N\,\ell\,\rho$ with coefficient map [`HeckeEis.binaryFormAlphaAdj`](def/HeckeEis_BinaryFormRep.html#L82) $\mathbb{Z}\,n\,\ell$ (namely: every parabolic cocycle $z$ admits a parabolic cocycle $w$ whose underlying function is that operator applied to $z$, with $T$ sending the class of $z$ to the class of $w$), the difference $T y - a(\ell)\, y$ lies in $p$ times the quotient.
--
--   This is the Deligne–Serre style passage from a complex Hecke eigenform to a mod-$p$ eigenclass, here realised in the integral parabolic cohomology of $\Gamma_0(N)$ with coefficients in binary forms of degree $n$, the eigenvalue congruence being read off modulo $p$ from the congruence modulo $\mathfrak{m}'$. It feeds the construction of mod-$p$ eigenclasses attached to ideals of the Hecke algebra, used in [`HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra`](thm.html#HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_eigenform.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_eigenform (N : ℕ) [NeZero N] (n : ℕ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]
    (Q : ℕ → Prop) (a : ℕ → ℤ)
    (𝔪' : Ideal (integralClosure ℤ ℂ)) (h𝔪' : 𝔪'.IsPrime) (hp𝔪' : (p : integralClosure ℤ ℂ) ∈ 𝔪')
    (α : ℕ → integralClosure ℤ ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (hf : f ≠ 0)
    (heigen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), Q ℓ →
      CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = ((α ℓ : integralClosure ℤ ℂ) : ℂ) • f)
    (hcong : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N → Q ℓ → α ℓ - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪') :
    ∃ y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      (¬ ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), y = (p : ℤ) • y') ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N → Q ℓ →
        ∀ T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℤ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
          ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), T y - (a ℓ : ℤ) • y = (p : ℤ) • y' := by sorry
