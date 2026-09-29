-- Prove2me | Theorems.Thm_ModularCurve_periodMap_traceLin
-- name    : ModularCurve.periodMap_traceLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/702eea12-0232-5508-b348-3cfe20128783
-- title:
--   Period map intertwines the level-lowering trace with the transfer
-- statement:
--   Let $M$ be a positive natural number and $q$ a natural number, let $W$ be an Atkin–Lehner datum for the pair $(M,q)$ — that is, a natural number $R = W.R$ together with a factorisation $M = qR$ and integers $a,b$ with $qa - Rb = 1$ — let $q$ be prime, and let $f$ be a weight-$2$ cusp form for $\Gamma_0(M)$. On one side stands the trace $\operatorname{traceLin} W\,hq$, the $\mathbb{C}$-linear map sending $f$ to the weight-$2$ cusp form for $\Gamma_0(R)$ whose underlying function is $f + \sum_{j<q} \bigl(f\mid_2 W.\mathrm{alGL}\bigr)\mid_2 \mathrm{heckeMatrix}\,q\,j$, where $W.\mathrm{alGL}$ is the Atkin–Lehner matrix attached to the datum. For a level $N$, $\operatorname{periodMap} N\,f$ is the additive homomorphism $\mathrm{Additive}(\Gamma_0(N)) \to \mathbb{C}$ given by the period homomorphism of a primitive $F$ of $f$ that is equivariant for $\Gamma_0(N)$, vanishes at $i\infty$, and has a limit at $i\infty$ along every $\delta \in \mathrm{SL}_2(\mathbb{Z})$ (and by $0$ if no such $F$ exists). The assertion is that $\operatorname{periodMap} R$ of the trace of $f$ equals the transfer, over the coset space $\Gamma_0(R)/\bigl(\Gamma_0(M)\cap\Gamma_0(R)\bigr)$ with $\gamma \mapsto \sum_{c} \varphi\bigl((\gamma\cdot c)_{\mathrm{out}}^{-1}\gamma\, c_{\mathrm{out}}\bigr)$, of the restriction $\varphi$ of $\operatorname{periodMap} M\,f$ along the inclusion of $\Gamma_0(M)$ viewed inside $\Gamma_0(R)$.
--
--   This is the Eichler–Shimura compatibility between the level-lowering trace on weight-$2$ cusp forms and the group-theoretic transfer (corestriction) on period homomorphisms. It is used in the proof that a Hecke word annihilating all relevant lattices kills the period homomorphism, via [`CuspForm.heckeWordHom_eq_zero_of_forall_newLattice`](thm.html#CuspForm.heckeWordHom_eq_zero_of_forall_newLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_traceLin.lean

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CongruenceSubgroup

theorem ModularCurve.periodMap_traceLin {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)
    (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    ModularCurve.periodMap W.R (CuspForm.traceLin W hq f) =
      HeckeEis.coresHom ((Gamma0 M).subgroupOf (Gamma0 W.R))
        (HeckeEis.pullbackHom ((Gamma0 W.R).subtype.subgroupComap (Gamma0 M))
          (ModularCurve.periodMap M f)) := by sorry
