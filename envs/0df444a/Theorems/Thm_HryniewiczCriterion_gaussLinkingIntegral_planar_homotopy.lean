-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_planar_homotopy
-- name    : HryniewiczCriterion.gaussLinkingIntegral_planar_homotopy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:54:59.753618+00:00
-- url     : https://prove2.me/theorems/4365914c-07f3-490c-a80e-a7a3cb17c792
-- title:
--   Gauss linking integrals of surface loops are invariant under $C^2$ homotopies of the parameter loop
-- statement:
--   Let $E:\mathbb R^2\to\mathbb R^4$ be $C^2$ on an open set $U$, let $K\subseteq U$ with $|E|=1$ on $K$, let $\gamma:\mathbb R\to S^3$ be a $C^2$ loop of period $1$ with $E(K)\cap\gamma(\mathbb R)=\emptyset$, and let $N\in S^3$ miss $\gamma$ and $E(K)$. If $L:\mathbb R^2\to\mathbb R^2$ is $C^2$, $1$-periodic in its second variable, and $L(\tau,s)\in K$ for $\tau\in[0,1]$, then the loops $E\circ L(0,\cdot)$ and $E\circ L(1,\cdot)$ have the same Gauss linking integral with $\gamma$ (`gaussLinkingIntegral`, stereographic projection from $N$).
--
--   Proof. Replace $\tau$ by $\phi(\tau)$ with $\phi$ the smooth transition function ($\phi=0$ on $(-\infty,0]$, $\phi=1$ on $[1,\infty)$, values in $[0,1]$), so the homotopy $E(L(\phi(\tau),s))$ is $C^2$ on all of $\mathbb R^2$, unit, and misses $N$ and $\gamma$ for every $\tau$; apply the fixed-pole homotopy invariance of the Gauss integral (published `gaussIntegral_eq_of_homotopy`).
-- source:
--   Homotopy invariance of the linking integral, e.g. D. Rolfsen, Knots and Links, Publish or Perish 1976, Ch. 5D

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_planar_homotopy (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (K : Set Plane) (hKU : K ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ K, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hKγ : ∀ v ∈ K, ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N) (hNE : ∀ v ∈ K, E v ≠ N)
    (L : ℝ → ℝ → Plane) (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hLper : ∀ τ s, L τ (s + 1) = L τ s) (hLK : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K) :
    gaussLinkingIntegral N (fun s => E (L 0 s)) γ = gaussLinkingIntegral N (fun s => E (L 1 s)) γ := by sorry
