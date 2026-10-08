-- Prove2me | Theorems.Thm_HryniewiczCriterion_windingInterval_reparam
-- name    : HryniewiczCriterion.windingInterval_reparam
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:53:37.014974+00:00
-- url     : https://prove2.me/theorems/42e3ae18-8dbb-4417-996d-5926144d2c4b
-- title:
--   The winding interval is invariant under reparametrization of $[0,1]$
-- statement:
--   Let $\varphi:\mathbb{R}\to M_2(\mathbb{R})$ be any matrix path, and let $\psi,\chi:[0,1]\to[0,1]$ be continuous with $\psi(0)=\chi(0)=0$, $\psi(1)=\chi(1)=1$ and $\psi\circ\chi=\mathrm{id}$ on $[0,1]$. Then the winding interval of Hryniewicz §2.1.1 does not change under reparametrization: $I(\varphi\circ\psi)=I(\varphi)$.
--
--   Proof idea: an angle lift $\theta$ of $\varphi$ gives the angle lift $\theta\circ\psi$ of $\varphi\circ\psi$, with the same endpoint values. Applying this to $\chi$ gives the reverse inclusion.
-- source:
--   Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5) (definition of the winding interval I(φ)); invariance under orientation-preserving reparametrization, used for time changes of periodic orbits as in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.31)–(3.32), p. 219.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.windingInterval_reparam (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ψ χ : ℝ → ℝ)
    (hψc : ContinuousOn ψ (Set.Icc 0 1)) (hψm : Set.MapsTo ψ (Set.Icc 0 1) (Set.Icc 0 1))
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 1)
    (hχc : ContinuousOn χ (Set.Icc 0 1)) (hχm : Set.MapsTo χ (Set.Icc 0 1) (Set.Icc 0 1))
    (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 1) (hψχ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ (χ t) = t) :
    windingInterval (fun t => φ (ψ t)) = windingInterval φ := by sorry
