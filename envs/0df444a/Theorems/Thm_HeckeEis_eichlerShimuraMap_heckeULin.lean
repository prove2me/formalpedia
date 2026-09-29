-- Prove2me | Theorems.Thm_HeckeEis_eichlerShimuraMap_heckeULin
-- name    : HeckeEis.eichlerShimuraMap_heckeULin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/86a702c9-a5e9-5ffc-8a19-ad22691fe76d
-- title:
--   Eichler–Shimura map intertwines U_ℓ for ℓ ∣ N
-- statement:
--   Fix $N \ge 1$ and $n \ge 0$, a prime $\ell$ with $\ell \mid N$, and write $\rho$ for the representation `(HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype`, i.e. the action of $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ by substitution on the space [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) of degree-$n$ homogeneous polynomials in two variables over $\mathbb{C}$. Here [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho$ is the quotient of the submodule of parabolic cocycles — functions $z : \Gamma_0(N) \to$ `BinaryForm ℂ n` with $z(gh) = z(g) + \rho(g)z(h)$ and $z(\gamma) \in \operatorname{range}(\rho(\gamma) - 1)$ whenever $\operatorname{tr}(\gamma)^2 = 4$ — by the coboundaries lying in it. Let $T$ be a $\mathbb{C}$-linear endomorphism of this quotient which is assumed to be induced by the cochain-level operator: for every parabolic cocycle $z$ there is a parabolic cocycle $w$ whose underlying function equals [`HeckeEis.coeffHeckeFun N ℓ`](def/Gamma0CoeffCohomology.html#L129) $\rho$ applied to $z$ with coefficient map [`HeckeEis.binaryFormAlphaAdj ℂ n ℓ`](def/HeckeEis_BinaryFormRep.html#L82) (substitution by $\mathrm{diag}(\ell,1)$), namely $g \mapsto \sum_{q \in \Gamma_0(N)/\,\mathrm{heckeUpper}\,N\,\ell} \rho((g\cdot q)^{\mathrm{out}})\bigl(a\,z(\mathrm{heckeConj}\,N\,\ell\,(\mathrm{transferAux}\;g\;q))\bigr)$, and such that $T[z] = [w]$. Then for every cusp form $f$ of weight $(n:\mathbb{Z})+2$ on $\Gamma_0(N)$ one has $T(\mathrm{ES}(f)) = \mathrm{ES}(U_\ell f)$, where $\mathrm{ES} =$ [`HeckeEis.eichlerShimuraMap n N`](def/HeckeEis_EichlerIntegral.html#L114) and $U_\ell =$ [`CuspForm.heckeULin ((n : ℤ) + 2) hℓN`](def/ModularForm_HeckeOperatorForms.html#L83).
--
--   This is the Hecke-equivariance of the Eichler–Shimura map at the primes dividing the level: the degeneracy operator $U_\ell$ on cusp forms of weight $n+2$ corresponds to the cochain-level Hecke operator at $\ell$ on parabolic cohomology with coefficients in binary forms of degree $n$. Together with the companion statement for primes not dividing $N$ it feeds [`HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime`](thm.html#HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime), which records equivariance simultaneously at all primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_eichlerShimuraMap_heckeULin.lean

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

theorem HeckeEis.eichlerShimuraMap_heckeULin (N : ℕ) [NeZero N] (n : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
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
      = HeckeEis.eichlerShimuraMap n N (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f) := by sorry
