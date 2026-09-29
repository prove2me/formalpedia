-- Prove2me | Theorems.Thm_ModularCurve_periodMap_heckeULin
-- name    : ModularCurve.periodMap_heckeULin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/3363f136-1322-5fe9-8b5c-200910aa68c9
-- title:
--   Period map intertwines U_q with the cohomological operator
-- statement:
--   Let $N$ be a positive natural number, let $q$ be a prime dividing $N$, and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$. Write $U_q f$ for [`CuspForm.heckeULin 2 hqN f`](def/ModularForm_HeckeOperatorForms.html#L83), the cusp form whose underlying function is $\sum_{j<q} f\mid[2]\,\mathrm{heckeMatrix}\,q\,j$, the weight-$2$ slash sum over the $q$ upper-triangular matrices with lower-right entry $q$. Write $\mathrm{periodMap}\,N$ for the additive homomorphism $\mathrm{Additive}(\Gamma_0(N)) \to \mathbb{C}$ attached to a weight-$2$ cusp form: it is the period homomorphism $\gamma \mapsto \mathrm{period}(\gamma)$ of a chosen function $F:\mathbb{H}\to\mathbb{C}$ satisfying `HasEquivariantPrimitive N f F` (namely $F\circ\mathrm{ofComplex}$ has derivative $f(\tau)$ at each $\tau$, $F\to 0$ at $i\infty$, $F$ is an equivariant primitive for $\Gamma_0(N)$, and $w\mapsto F(\delta\cdot w)$ has a limit at $i\infty$ for every $\delta\in\mathrm{SL}_2(\mathbb{Z})$), and $0$ if no such $F$ exists. Finally [`HeckeEis.heckeOperatorHom N q ℂ`](def/Gamma0HeckeOperatorHom.html#L285) is the endomorphism of $\mathrm{Hom}(\mathrm{Additive}(\Gamma_0(N)),\mathbb{C})$ obtained by pulling back along the homomorphism `heckeConj N q` from the subgroup `heckeUpper N q` of $\Gamma_0(N)$ and then applying the transfer-style corestriction `coresHom` back to $\Gamma_0(N)$. The assertion, with the instance $q\neq 0$ extracted from the primality of $q$, is the identity $\mathrm{periodMap}_N(U_q f) = \mathrm{heckeOperatorHom}(N,q,\mathbb{C})\bigl(\mathrm{periodMap}_N(f)\bigr)$.
--
--   This is the Hecke equivariance of the Eichler–Shimura period map at a prime dividing the level, where the operator on cusp forms is $U_q$ rather than $T_q$ and the cohomological side has $q$ cosets. It feeds the construction of the Eichler–Shimura map into $H^1$ and the embedding of the Hecke algebra into endomorphisms of spaces of parabolic homomorphisms, and is used in comparing complex and integral linear independence of cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_heckeULin.lean

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.periodMap_heckeULin {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeULin 2 hqN f)
      = HeckeEis.heckeOperatorHom N q ℂ (ModularCurve.periodMap N f) := by sorry
