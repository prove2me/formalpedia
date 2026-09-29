-- Prove2me | Theorems.Thm_ModularCurve_heckeDivBar_self_add_atkinLehner_smul
-- name    : ModularCurve.heckeDivBar_self_add_atkinLehner_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/83b68136-f4c9-5496-99c5-5e4526cc2748
-- title:
--   Atkin–Lehner relation U_q D + w_q· D = β^*α_*D on divisors
-- statement:
--   Fix natural numbers $N$ and $q$ with $N$ nonzero, $q$ prime and $q \nmid N$, and work over $L = \overline{\mathbb Q}$ throughout; all function fields are the base-changed modular fields $\mathrm{modularFunctionFieldBar}(M) = \mathrm{laurentBaseChange}\,L\,(\mathrm{modularFunctionFieldFull}\,M)$, and a divisor is a finitely supported $\mathbb Z$-valued function on the places of such a field over $L$. Assume: the two degeneracy maps from level $Nq$ to level $Nq\cdot q$, namely the inclusion `heckeAlphaBar` and the $q$-substitution `heckeBetaBar`, have integral underlying ring homomorphisms (hypotheses $h\alpha$, $h\beta$); the corresponding integrality holds for the two maps from level $N$ to level $Nq$ ($h\alpha N$, $h\beta N$); and the fields at levels $Nq\cdot q$ and $Nq$ satisfy `HasPrincipalDivisors`, i.e. every nonzero element has a degree-zero divisor whose value at each place is the order of the element there. Then for every divisor $D$ at level $Nq$, the correspondence $\mathrm{heckeDivBar}$, which pulls $D$ back along the $q$-substitution into level $Nq\cdot q$ and pushes it forward along the inclusion, plus the translate of $D$ by the automorphism of the level-$Nq$ field obtained by base change (`geomAut`) from `atkinLehnerInvolutionFull N q` — a chosen $\mathbb Q$-automorphism of $\mathrm{modularFunctionFieldFull}(Nq)$ satisfying `IsAtkinLehnerAutFull N q` when one exists, the identity otherwise — equals the pullback along the $q$-substitution from level $N$ of the pushforward of $D$ along the inclusion of level $N$ into level $Nq$.
--
--   This is the Atkin–Lehner (Mackey) relation $U_q + w_q = \beta^{*}\alpha_{*}$ at a prime $q$ dividing the level exactly once, formulated on divisors of $X_0(Nq)$ over $\overline{\mathbb Q}$ rather than on the Jacobian. It is the divisor-level input for the corresponding identity of endomorphisms of $\mathrm{Pic}^0$ obtained by descent, and for the statements controlling specialisation of places under the Hecke correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDivBar_self_add_atkinLehner_smul.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeDivBar_self_add_atkinLehner_smul (N q : ℕ) [NeZero N] [Fact q.Prime]
    (hqN : ¬ q ∣ N)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * q))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hαN : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβN : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    heckeDivBar hα hβ D
        + (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)) • D =
      Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβN
        (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαN D) := by sorry
