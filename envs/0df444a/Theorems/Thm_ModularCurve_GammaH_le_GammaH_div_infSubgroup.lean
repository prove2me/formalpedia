-- Prove2me | Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
-- name    : ModularCurve.GammaH_le_GammaH_div_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/da4840b1-827f-587a-b159-dfb1fb385ace
-- title:
--   Γ_H(M)≤Γ_{H'}(M/p) for H' the reduction of H
-- statement:
--   Let $p$ and $M$ be natural numbers with $p$ prime and $M$ nonzero, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $hpM$ be a proof that $p \mid M$. Here [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) denotes the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(M)$ into $\mathrm{SL}_2(\mathbb{Z})$, of the preimage of $H$ under the homomorphism [`CohCarrier.gamma0Units M`](def/CohCarrier_Level.html#L121) which sends $\gamma \in \Gamma_0(M)$ to the unit of $\mathbb{Z}/M$ with value the reduction of the lower-right entry $\gamma_{11}$ and inverse the reduction of $\gamma_{00}$; thus it consists of those $\gamma \in \Gamma_0(M)$ whose lower-right entry mod $M$ lies in $H$. Further, `infSubgroup p M H hpM` is the image of $H$ under the reduction map $\mathbb{Z}\mathrm{Mod}.\mathrm{unitsMap}$ on unit groups attached to the divisibility $(M/p) \mid M$, a subgroup of $(\mathbb{Z}/(M/p))^\times$. The assertion is the inclusion of subgroups of $\mathrm{SL}_2(\mathbb{Z})$: $\Gamma_H(M) \le \Gamma_{H'}(M/p)$, where $H'$ is that image.
--
--   This is the group-theoretic input to the degeneracy comparison between level $M$ and level $M/p$: it says that the $H$-level structure at level $M$ refines the one obtained by reducing $H$ modulo $M/p$, so that function fields and differentials at level $M/p$ pull back to level $M$. It is used throughout the treatment of the modular curves $X_H$ and their differentials mod $\ell$, for instance in the construction of degeneracy embeddings and in the local study of $X_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.GammaH_le_GammaH_div_infSubgroup
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by sorry
