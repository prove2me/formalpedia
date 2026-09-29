-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd
-- name    : ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/51d19148-8e63-5a1a-972f-f2223d01df3d
-- title:
--   U_q scales the period homomorphism of an eigenform by a_q
-- statement:
--   Let $N$ be a natural number and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ which is a normalised eigenform in the sense of the project's predicate `IsNormalizedEigenform`: writing $a_n =$ `qCoeff f n` for the $n$-th coefficient of the $q$-expansion of $f$ at width $1$, one has $a_1 = 1$, $a_{mn} = a_m a_n$ for coprime $m, n$, $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for every prime $p \nmid N$ and every $r$, and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for every prime $p \mid N$ and every $r$. Let $q$ be a prime dividing $N$. The assertion concerns the period homomorphism [`ModularCurve.periodMap N f`](def/ModularCurve_PeriodMapBundled.html#L20) $\colon \mathrm{Additive}(\Gamma_0(N)) \to \mathbb{C}$, defined as the period homomorphism $\gamma \mapsto F(\gamma\cdot z) - F(z)$ of a chosen $F \colon \mathcal{H} \to \mathbb{C}$ which is an equivariant primitive of $f$ for $\Gamma_0(N)$ (its derivative is $f$ at every point, it tends to $0$ at $i\infty$, and $F \circ \delta$ has a limit at $i\infty$ for every $\delta \in \mathrm{SL}_2(\mathbb{Z})$), and as $0$ if no such $F$ exists. The conclusion is that the operator [`HeckeEis.heckeOperatorHom N q ℂ`](def/Gamma0HeckeOperatorHom.html#L285), namely pullback along the conjugation homomorphism `heckeConj N q` from `heckeUpper N q` to $\Gamma_0(N)$ followed by the transfer (corestriction) back to $\Gamma_0(N)$, sends [`ModularCurve.periodMap N f`](def/ModularCurve_PeriodMapBundled.html#L20) to $a_q \cdot$ [`ModularCurve.periodMap N f`](def/ModularCurve_PeriodMapBundled.html#L20).
--
--   This is the Hecke equivariance of the period (Eichler–Shimura) map at a prime dividing the level: the homomorphism-level operator $U_q$ acts on the period class of a weight-$2$ normalised eigenform through its $q$-th Fourier coefficient. It is used in the construction of parabolic realisations of the period homomorphism, via [`ModularCurve.Period.exists_parabolicRealization`](thm.html#ModularCurve.Period.exists_parabolicRealization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd.lean

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime)
    (hqN : q ∣ N) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    HeckeEis.heckeOperatorHom N q ℂ (ModularCurve.periodMap N f)
      = (ModularFormClass.qCoeff f q) • ModularCurve.periodMap N f := by sorry
