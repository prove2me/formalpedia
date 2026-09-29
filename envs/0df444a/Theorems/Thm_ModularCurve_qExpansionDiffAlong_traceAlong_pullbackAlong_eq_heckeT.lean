-- Prove2me | Theorems.Thm_ModularCurve_qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT
-- name    : ModularCurve.qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/83fde0b7-44fc-5ffc-a4da-e3e3e7108c39
-- title:
--   Degeneracy trace acts as formal T_q on q-expansions
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ with $p$ prime, let $N \ge 1$ and let $q$ be a prime, and assume $p \nmid Nq$ and $q \nmid N$; let $\zeta$ be a unit of $K$ whose image in $K$ is a primitive $q$-th root of unity, and let $\omega$ be a Kähler differential in $\Omega[F_N/K]$, where $F_N =$ `modularFunctionFieldC K N` is the intermediate field of the Laurent series field `LaurentSeries K` obtained by adjoining $\{$`jqModC K`$,$ `jqNModC K N`$\}$ to $K$. Inside the roof field `charLDegeneracyRoof K N q`, obtained by adjoining $\{$`jqModC K`$,$ `jqNModC K N`$,$ `jqNModC K q`$,$ `jqNModC K (N*q)`$\}$, sit two $K$-algebra embeddings of $F_N$: `heckeAlphaC`, the inclusion, and `heckeBetaC`, whose underlying map on Laurent series is the substitution `qExpand K q`. The assertion is the equality in `LaurentSeries K` of two series: on the left, the $q$-expansion (the $K$-linear map `qExpansionDiffAlong` attached to the inclusion $(F_N)$`.val` of $F_N$ into `LaurentSeries K`, i.e. the chosen map satisfying `IsQExpansionDiffAlong` for that embedding, and $0$ if none exists) of the differential obtained from $\omega$ by first pulling back along `heckeBetaC` (`KaehlerDifferential.map` for the algebra structure given by that embedding) and then applying the trace map `Differential.traceAlong` for `heckeAlphaC` (defined, when the extension is separable, via the base-change isomorphism of Kähler differentials for formally étale extensions together with `Algebra.trace`); on the right, [`LaurentSeries.heckeT K q _ 2`](def/LaurentSeries_HeckeV.html#L39), that is $U_q + (q:K)^{2-1}\,V_q$, applied to the $q$-expansion of $\omega$, so the $n$-th coefficient is $a_{qn} + q\,a_{n/q}$ (the second term present only when $q \mid n$).
--
--   This is the statement that the Hecke correspondence $\operatorname{tr}_\alpha \circ \beta^{*}$ on differentials of the modular curve of level $N$ in characteristic $p$ acts on $q$-expansions as the formal weight-two Hecke operator $T_q = U_q + q V_q$. It is the operator-level form of the corresponding coefficient computation, and is used in reading the Hecke action on the $p$-torsion of $\operatorname{Pic}^0$ through differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_LaurentSeries_HeckeV

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve AlgebraicCurve

theorem ModularCurve.qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT
    (K : Type*) [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hpNq : ¬ p ∣ N * q) (hqN : ¬ q ∣ N)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    qExpansionDiffAlong (modularFunctionFieldC K N).val
        (Differential.traceAlong (heckeAlphaC K N q) (Differential.pullbackAlong (heckeBetaC K N q) ω))
      = LaurentSeries.heckeT K q (Fact.out : q.Prime).pos 2
          (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) := by sorry
