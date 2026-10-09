-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_ne_zero_of_transverse_disk
-- name    : HryniewiczCriterion.gaussLinkingIntegral_ne_zero_of_transverse_disk
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T17:59:15.651516+00:00
-- url     : https://prove2.me/theorems/f4145e70-dede-4092-ab71-5a394c018f0f
-- title:
--   A knot crossing a disk transversally, always from the same side and at least once, has non-zero Gauss linking number with the disk's boundary
-- statement:
--   Let $E:\mathbb{R}^2\to\mathbb{R}^4$ be $C^2$ on an open neighbourhood of the closed unit disk $\overline{\mathbb D}$ with $|E|=1$ on $\overline{\mathbb D}$, so $E(\overline{\mathbb D})\subset S^3$. Let $u:\mathbb{R}\to S^1$ be a $C^2$, $1$-periodic immersion ($u'\neq0$), so $s\mapsto E(u(s))$ runs (possibly several times) around $E(S^1)$. Let $\gamma:\mathbb{R}\to S^3$ be a $C^2$, $1$-periodic loop that is injective modulo $1$ (a knot). Assume:
--
--   1. $\gamma$ misses the boundary loop: $E(u(s))\neq\gamma(t)$ for all $s,t$;
--   2. $\gamma$ crosses the disk transversally, always from the same side: for a fixed $\sigma\in\mathbb{R}$,
--   $$\sigma\cdot\det\big(\gamma(t),\ \gamma'(t),\ \partial_1E(v),\ \partial_2E(v)\big)>0\quad\text{whenever }v\in\overline{\mathbb D},\ E(v)=\gamma(t);$$
--   3. $\gamma$ meets $E(\overline{\mathbb D})$ at least once.
--
--   Then there is a unit vector $N$ missing both loops such that the Gauss linking integral `gaussLinkingIntegral N (E ∘ u) γ` (stereographic projection from $N$) is a non-zero integer.
--
--   This is the statement "the linking number of a knot with the boundary of a surface equals the algebraic intersection number of the knot with the surface", in the special case where all intersections have the same sign. The algebraic count is then $\pm\deg(u)\cdot\#\{t\in[0,1):\gamma(t)\in E(\overline{\mathbb D})\}\neq0$. Here $E$ need not be injective, and $\det$ is the $4\times4$ determinant with the four vectors as rows, which orients the disk relative to $\gamma$ inside $S^3$.
--
--   Suggested proof. The crossings are finitely many interior points $v_j$, by transversality and compactness. Choose a centre $c$ in the open disk so that the $v_j$ lie on distinct rays from $c$; the bad centres form finitely many lines. Work in the strip coordinates $(\lambda,s)\mapsto c+\lambda(u(s)-c)$, $\lambda\in[0,1]$. Graph loops $s\mapsto E(c+h(s)(u(s)-c))$ interpolate between $h\equiv1$ (the boundary loop) and $h\equiv0$ (a constant loop, Gauss integral $0$). Use bump functions to move $h$ past one crossing at a time. Each move changes the Gauss integral by the Gauss integral of a small loop around that crossing: arcs with fixed endpoints can be homotoped freely, since the boundary terms of the variation formula vanish. A small loop on a transverse surface around a knot has Gauss integral $\pm1$, with the sign given by condition 2 and by the orientation of $u$, which is the same at every crossing.
-- source:
--   D. Rolfsen, Knots and Links, Publish or Perish 1976, Ch. 5D (linking number = algebraic intersection number with a Seifert surface); U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, proof of Lemma 3.12 (p. 26), where $\operatorname{lk}(P,Q)\neq0$ is read off from the intersections of $Q$ with a page.

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_ne_zero_of_transverse_disk (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (u : ℝ → Plane) (hu : ContDiff ℝ 2 u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hu' : ∀ s, deriv u s ≠ 0)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hγinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (hbd : ∀ s t, E (u s) ≠ γ t) (σ : ℝ)
    (htr : ∀ t, ∀ v ∈ closedUnitDisk, E v = γ t →
      0 < σ * Matrix.det (Matrix.of ![γ t, deriv γ t,
        fderiv ℝ E v (Pi.single 0 1), fderiv ℝ E v (Pi.single 1 1)]))
    (hcross : ∃ t, ∃ v ∈ closedUnitDisk, E v = γ t) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ s, E (u s) ≠ N ∧ γ s ≠ N) ∧
      ∃ n : ℤ, n ≠ 0 ∧ gaussLinkingIntegral N (fun s => E (u s)) γ = n := by sorry
