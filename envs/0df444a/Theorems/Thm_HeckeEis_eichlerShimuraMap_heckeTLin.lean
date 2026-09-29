-- Prove2me | Theorems.Thm_HeckeEis_eichlerShimuraMap_heckeTLin
-- name    : HeckeEis.eichlerShimuraMap_heckeTLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e1b2d32e-efa3-5984-adbe-20ce258706cb
-- title:
--   Eichler–Shimura map intertwines T_ℓ with cohomological T_ℓ
-- statement:
--   Fix $N \ge 1$ and $n \ge 0$, a prime $\ell$ with $\ell \nmid N$, and write $\rho$ for the representation of $\Gamma_0(N)$ obtained by restricting along $\Gamma_0(N) \hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ the substitution action [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) of $\mathrm{SL}(2,\mathbb{Z})$ on the space of degree-$n$ homogeneous polynomials in two variables over $\mathbb{C}$. Let $T$ be any $\mathbb{C}$-linear endomorphism of [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho$, the quotient of the module of parabolic cocycles — functions $z : \Gamma_0(N) \to \mathrm{Sym}^n$ with $z(gh) = z(g) + \rho(g)z(h)$ and $z(\gamma) \in \mathrm{range}(\rho(\gamma) - 1)$ whenever $\mathrm{tr}(\gamma)^2 = 4$ — by the submodule of those parabolic cocycles which are coboundaries. Assume $T$ is induced by the cochain-level Hecke operator: for every parabolic cocycle $z$ there is a parabolic cocycle $w$ whose underlying function equals [`HeckeEis.coeffHeckeFun N ℓ`](def/Gamma0CoeffCohomology.html#L129) $\rho$ applied to $z$ with coefficient map [`HeckeEis.binaryFormAlphaAdj ℂ n ℓ`](def/HeckeEis_BinaryFormRep.html#L82) (substitution by $\mathrm{diag}(\ell,1)$), i.e. the coset sum $g \mapsto \sum_{q} \rho((g\cdot q)^{\mathrm{out}})\,\alpha\bigl(z(\mathrm{heckeConj}(\mathrm{transferAux}\,g\,q))\bigr)$ over $\Gamma_0(N)/\mathrm{heckeUpper}(N,\ell)$, and such that $T[z] = [w]$. Then for every cusp form $f$ of weight $(n:\mathbb{Z})+2$ on $\Gamma_0(N)$ one has $T(\mathrm{ES}(f)) = \mathrm{ES}(T_\ell f)$, where $\mathrm{ES} =$ [`HeckeEis.eichlerShimuraMap n N`](def/HeckeEis_EichlerIntegral.html#L114) and $T_\ell =$ [`CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN`](def/ModularForm_HeckeOperatorForms.html#L69).
--
--   This is the Hecke-equivariance of the Eichler–Shimura map from weight $n+2$ cusp forms on $\Gamma_0(N)$ to parabolic cohomology with coefficients in binary forms of degree $n$, stated for an arbitrary endomorphism $T$ of the cohomology that is induced by the explicit coset-sum Hecke operator on cocycles, so that no existence or uniqueness statement for the induced operator is needed. It supports the construction of integral and mod $p$ eigenclasses in parabolic cohomology attached to Hecke eigenforms and the finiteness of the relevant Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_eichlerShimuraMap_heckeTLin.lean

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

theorem HeckeEis.eichlerShimuraMap_heckeTLin (N : ℕ) [NeZero N] (n : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ]
      HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n))
              = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
            T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    T (HeckeEis.eichlerShimuraMap n N f)
      = HeckeEis.eichlerShimuraMap n N (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f) := by sorry
