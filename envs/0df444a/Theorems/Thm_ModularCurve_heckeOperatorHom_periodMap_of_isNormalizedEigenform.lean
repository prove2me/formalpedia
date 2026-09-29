-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform
-- name    : ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/5b726213-3e43-5c2d-9f70-6c5a08205605
-- title:
--   Hecke operator acts on the period class by a_ℓ(f)
-- statement:
--   Let $N$ be a natural number and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ which is a normalised eigenform in the sense of the project predicate `IsNormalizedEigenform`, i.e. its $q$-expansion coefficients $a_n =$ `qCoeff f n` (the coefficients of the $q$-expansion of $f$ with width $1$) satisfy $a_1 = 1$, $a_{mn} = a_m a_n$ for coprime $m,n$, the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for every prime $p \nmid N$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for every prime $p \mid N$. Let $\ell$ be a prime with $\ell \nmid N$. Then the endomorphism [`HeckeEis.heckeOperatorHom N ℓ ℂ`](def/Gamma0HeckeOperatorHom.html#L285) of the group of additive homomorphisms $\mathrm{Additive}(\Gamma_0(N)) \to \mathbb{C}$ — pullback along the homomorphism `heckeConj N ℓ` from the subgroup `heckeUpper N ℓ` of $\Gamma_0(N)$ into $\Gamma_0(N)$, followed by the corestriction (transfer-type sum over the cosets of `heckeUpper N ℓ`) — sends [`ModularCurve.periodMap N f`](def/ModularCurve_PeriodMapBundled.html#L20) to $a_\ell \cdot$ [`ModularCurve.periodMap N f`](def/ModularCurve_PeriodMapBundled.html#L20). Here `periodMap N f` is the period homomorphism $\gamma \mapsto$ (period of $F$ at $\gamma$) attached to a chosen $F : \mathbb{H} \to \mathbb{C}$ with derivative $f$, vanishing limit at $i\infty$, equivariant-primitive for $\Gamma_0(N)$ and having a limit along $\delta \cdot w$ at $i\infty$ for every $\delta \in \mathrm{SL}_2(\mathbb{Z})$, and is $0$ if no such $F$ exists.
--
--   This is the Hecke equivariance of the Eichler–Shimura period map in weight $2$, specialised to an eigenform: the period class of $f$ is an eigenvector of the group-cohomological Hecke operator $T_\ell$ with the same eigenvalue $a_\ell(f)$. It is used in the construction of a parabolic realisation of the eigensystem of $f$ ([`ModularCurve.Period.exists_parabolicRealization`](thm.html#ModularCurve.Period.exists_parabolicRealization)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform.lean

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f)
      = (ModularFormClass.qCoeff f ℓ) • ModularCurve.periodMap N f := by sorry
