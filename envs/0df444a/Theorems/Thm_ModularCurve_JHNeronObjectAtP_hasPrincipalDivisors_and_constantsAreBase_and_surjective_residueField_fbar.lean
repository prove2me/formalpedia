-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
-- name    : ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/4d0f464c-3a4a-5254-84dc-0f850aa2722b
-- title:
--   Principal divisors, constants and rational places of ̄ F
-- statement:
--   Fix a prime $p$, a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and assume $p \mid M$ and $p^2 \nmid M$; let $\kappa$ be an algebraically closed field of characteristic $p$. Write $\bar F =$ `Fbar p M H hpM κ` for the $q$-expansion function field $\kappa$-algebra `qExpFunctionFieldC κ (ΓN p M H hpM)` attached to the subgroup `ΓN p M H hpM` of $\mathrm{SL}_2(\mathbb{Z})$ determined by $p$, $M$ and $H$. Three assertions are made about the extension $\kappa \subseteq \bar F$. First, `HasPrincipalDivisors`: for every $f \in \bar F$ with $f \neq 0$ there is a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on the places of $\bar F$ over $\kappa$, a place being a proper valuation subring of $\bar F$ containing $\kappa$ whose ring is a principal ideal ring) with $D(v) = \mathrm{ord}_v(f)$ for every place $v$ and $\deg D = 0$. Second, `ConstantsAreBase`: the Riemann–Roch space $L(0)$ of the zero divisor coincides with the image of $\kappa$ in $\bar F$. Third, for every place $v$ the map $\kappa \to \kappa(v)$ into the residue field of $v$ is surjective, i.e. every place is rational.
--
--   This records that the $q$-expansion function field of the relevant modular curve over an algebraically closed field of characteristic $p$ is a one-variable function field with full constant field and only rational places. It supplies the standing hypotheses for the divisor- and Picard-group computations on the characteristic-$p$ fibre used in the study of the Néron model of $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open AlgebraicCurve

theorem ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] :
    HasPrincipalDivisors κ (Fbar p M H hpM κ) ∧ ConstantsAreBase κ (Fbar p M H hpM κ) ∧
      ∀ v : Place κ (Fbar p M H hpM κ), Function.Surjective (algebraMap κ v.ResidueField) := by sorry
