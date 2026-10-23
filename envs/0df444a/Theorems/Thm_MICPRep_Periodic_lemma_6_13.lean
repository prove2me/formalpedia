-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_13
-- name    : MICPRep.Periodic.lemma_6_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:28.243029+00:00
-- url     : https://prove2.me/theorems/bac622a0-2a33-4047-91b4-74a7f976be9c
-- title:
--   Lemma 6.13, p. 30 — each integer recession direction r gives a unique asymptotic direction u, and for u = 0 the unions along z + rℝ₊ are convex with diameter at most D_MICP(M)
-- statement:
--   Let $M \subseteq \mathbb R^{n+p+d}$ be closed and convex, inducing a rational MICP formulation with index set $I$ and $z$-projected sets $\{A_z\}$. Assume $D_{\mathrm{MICP}}(M) < \infty$ and $I_{\mathbb Z}$ has an integer point in its relative interior. Then for every $r \in \mathbb Z^d \cap (I_\infty \setminus\{0\})$ there is a unique $u \in \mathbb R^n$ with
--   $$x + \lambda u \in \mathrm{cl}(A_{z + \lambda r}) \qquad \forall \lambda > 0,\ z \in \mathbb Z^d \cap I,\ x \in A_z. \tag{6.26}$$
--   Furthermore, if $u = 0$, then for every $z \in \mathbb Z^d \cap I$ the set $\tilde A_z = \bigcup_{z' \in z + r\mathbb R_+} A_{z'}$ is convex, $D(\tilde A_z) \le D_{\mathrm{MICP}}(M)$, and
--   $$\bigcup_{z' \in (z + r\mathbb R_+) \cap \mathbb Z^d} A_{z'} \subseteq \tilde A_z \subseteq \bigcup_{z' \in (z + r\mathbb R_+)\cap\mathbb Z^d} \mathrm{cl}(A_{z'}).$$
--
--   Either the recession direction produces a nearly periodic formulation ($u \neq 0$) or the integer variable along $r$ can be relaxed without increasing the diameter ($u = 0$); this is the dichotomy behind Lemma 6.2.
--
--   **Formalization Note** $\lambda > 0$ ranges over the reals, $\mathbb R_+ = [0, \infty)$, and diameters are extended (`Metric.ediam`). "If $u = 0$" is stated as: for every $u$ satisfying (6.26), if $u = 0$ then the conclusions hold.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 30, Lemma 6.13 and (6.26)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.13, p. 30. -/
theorem lemma_6_13 {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hD : micpDiam M < ⊤)
    (hint : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty)
    (r : Fin d → ℝ) (hrZ : r ∈ intLattice d) (hrI : r ∈ recCone (indexSet M)) (hr0 : r ≠ 0) :
    (∃! u : Pt n, ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M, ∀ x ∈ zProj M z,
        x + t • u ∈ closure (zProj M (z + t • r))) ∧
    ∀ u : Pt n, (∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M, ∀ x ∈ zProj M z,
        x + t • u ∈ closure (zProj M (z + t • r))) → u = 0 →
      ∀ z ∈ intLattice d ∩ indexSet M,
        Convex ℝ (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ∧
        Metric.ediam (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ≤ micpDiam M ∧
        (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r} ∩ intLattice d, zProj M z') ⊆
          (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ∧
        (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ⊆
          ⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r} ∩ intLattice d,
            closure (zProj M z') := by sorry

end MICPRep.Periodic
