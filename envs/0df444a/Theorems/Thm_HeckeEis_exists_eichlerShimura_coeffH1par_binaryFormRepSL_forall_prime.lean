-- Prove2me | Theorems.Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime
-- name    : HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/fd78cd2e-b041-5f16-998b-018ae96c81f7
-- title:
--   Hecke-equivariant Eichler–Shimura decomposition of parabolic cohomology
-- statement:
--   Let $N \ge 1$ and $n \ge 0$ be natural numbers, and let $\rho$ be the representation of $\Gamma_0(N)$ on the space $\mathrm{BinaryForm}\,\mathbb{C}\,n$ of homogeneous degree-$n$ polynomials in $\mathbb{C}[X_0,X_1]$ obtained by restricting [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}_2(\mathbb{Z})$, where $g$ acts by the substitution $X_j \mapsto \sum_i g_{ij} X_i$. Write $H^1_{\mathrm{par}}(\rho)$ for [`HeckeEis.coeffH1par ρ`](def/Gamma0CoeffCohomology.html#L100), the quotient of the submodule of functions $z \colon \Gamma_0(N) \to \mathrm{BinaryForm}\,\mathbb{C}\,n$ satisfying the cocycle identity $z(gh) = z(g) + \rho(g)z(h)$ and the parabolicity condition $z(\gamma) \in \mathrm{range}(\rho(\gamma) - 1)$ for every $\gamma$ with $\mathrm{tr}(\gamma)^2 = 4$, by the coboundaries lying in it; [`HeckeEis.coeffH1parMk`](def/Gamma0CoeffCohomology.html#L111) denotes the quotient map. The theorem asserts the existence of a $\mathbb{C}$-linear map $\mathrm{ES}$ and a map $\overline{\mathrm{ES}}$ semilinear for complex conjugation, both from $S_{n+2}(\Gamma_0(N))$, the cusp forms of weight $(n:\mathbb{Z})+2$ for $\Gamma_0(N)$, to $H^1_{\mathrm{par}}(\rho)$, such that: both are injective; their ranges are complementary submodules of $H^1_{\mathrm{par}}(\rho)$; and, for every prime $\ell$ and every $\mathbb{C}$-linear endomorphism $T$ of $H^1_{\mathrm{par}}(\rho)$ which is induced at cocycle level by [`HeckeEis.coeffHeckeFun N ℓ ρ (HeckeEis.binaryFormAlphaAdj ℂ n ℓ)`](def/Gamma0CoeffCohomology.html#L129) — that is, for each parabolic cocycle $z$ there is a parabolic cocycle $w$ whose underlying function is the transfer-type sum $g \mapsto \sum_{q \in \Gamma_0(N)/\mathrm{heckeUpper}\,N\,\ell} \rho((g \cdot q)^{\mathrm{out}})\bigl(F \mapsto F(\ell X_0, X_1)\bigr)\bigl(z(\mathrm{heckeConj}\,N\,\ell\,(\mathrm{transferAux}\,\cdots))\bigr)$ applied to $z$, with $T[z] = [w]$ — one has $T \circ \mathrm{ES} = \mathrm{ES} \circ \mathrm{heckeTLin}$ and $T \circ \overline{\mathrm{ES}} = \overline{\mathrm{ES}} \circ \mathrm{heckeTLin}$ when $\ell \nmid N$, and the same two identities with [`CuspForm.heckeULin`](def/ModularForm_HeckeOperatorForms.html#L83) in place of [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) when $\ell \mid N$, where on cusp forms $\mathrm{heckeULin}$ is $f \mapsto \sum_{j<\ell} f \mid_{k} \mathrm{heckeMatrix}\,\ell\,j$ and $\mathrm{heckeTLin}$ adds to this the term $f \mid_{k} \mathrm{heckeDiagMatrix}\,\ell$.
--
--   This is the Eichler–Shimura decomposition in weight $n+2$, presented as an explicit pair of injections of $S_{n+2}(\Gamma_0(N))$ into parabolic group cohomology with complementary images, compatible with the Hecke action at every prime: $T_\ell$ for $\ell \nmid N$ and $U_\ell$ for $\ell \mid N$. It is used to transport the Hecke action on cusp forms to a lattice-theoretic setting, and is cited in the construction of an integral structure on cusp forms of weight at least two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime (N : ℕ) [NeZero N] (n : ℕ) :
    ∃ (ES : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ]
          HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
      (ESbar : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₛₗ[starRingEnd ℂ]
          HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      Function.Injective ES ∧ Function.Injective ESbar ∧
      IsCompl (LinearMap.range ES) (LinearMap.range ESbar) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
        (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ES f) = ES (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f)) ∧
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ESbar f) = ESbar (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f))) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
        (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ES f) = ES (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f)) ∧
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ESbar f) = ESbar (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f))) := by sorry
