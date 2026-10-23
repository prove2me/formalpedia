-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_11
-- name    : MICPRep.Periodic.lemma_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:24.778+00:00
-- url     : https://prove2.me/theorems/9b700677-5d84-47f8-9931-8c1c6f6ec691
-- title:
--   Lemma 6.11, p. 29 — f_c convex, g_c and w_c concave as extended-real functions of z, and sup of w_c over integer points of I_ℤ is finite iff over I_ℤ
-- statement:
--   Let $M \subseteq \mathbb R^{n+p+d}$ be closed and convex, inducing an MICP formulation with index set $I$ and $z$-projected sets $\{A_z\}_{z \in I}$. For $c \in \mathbb R^n$ define $g_c, f_c, w_c : I \to \mathbb R \cup\{-\infty, +\infty\}$ by
--   $$f_c(z) = -\sigma_{A_z}(-c) = \inf\{c^{\mathsf T}x : x \in A_z\}, \quad g_c(z) = \sigma_{A_z}(c) = \sup\{c^{\mathsf T}x : x \in A_z\}, \quad w_c(z) = g_c(z) - f_c(z).$$
--   Then $f_c$ is convex and $g_c$, $w_c$ are concave on $I$, and for all $z \in I$: $f_c(z) < \infty$, $g_c(z) > -\infty$, $w_c(z) \ge 0$. If, in addition, $I_{\mathbb Z}$ has an integer point in its relative interior, then for every $c \in \mathbb R^n$
--   $$\sup_{z \in I_{\mathbb Z} \cap \mathbb Z^d} w_c(z) < \infty \iff \sup_{z \in I_{\mathbb Z}} w_c(z) < \infty. \tag{6.25}$$
--
--   The width functions $w_c$ measure the extent of the $z$-projected sets in direction $c$; (6.25) transfers finiteness of the MICP diameter from integer to all points of $I_{\mathbb Z}$.
--
--   **Formalization Note** Values are in `EReal`; $f_c$ may be $-\infty$ and $g_c$ may be $+\infty$ at non-integer $z$ (the paper's Example 6.1). Convexity is the explicit inequality $f(tz^1 + (1-t)z^2) \le t f(z^1) + (1-t) f(z^2)$ for $t \in [0,1]$ in `EReal` (where $0\cdot(\pm\infty) = 0$, so the endpoints are identities), and the reverse inequality for concavity. $w_c = g_c - f_c$ never meets $\infty - \infty$ on $I$.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 29, Lemma 6.11 and (6.25)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.11, p. 29. -/
theorem lemma_6_11 {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : Induces M S) :
    let I := indexSet M
    let f : Pt n → (Fin d → ℝ) → EReal := fun c z => -supportFn (zProj M z) (-c)
    let g : Pt n → (Fin d → ℝ) → EReal := fun c z => supportFn (zProj M z) c
    let w : Pt n → (Fin d → ℝ) → EReal := fun c z => g c z - f c z
    (∀ c : Pt n, ∀ z₁ ∈ I, ∀ z₂ ∈ I, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        f c (t • z₁ + (1 - t) • z₂) ≤ (t : EReal) * f c z₁ + ((1 - t : ℝ) : EReal) * f c z₂ ∧
        (t : EReal) * g c z₁ + ((1 - t : ℝ) : EReal) * g c z₂ ≤ g c (t • z₁ + (1 - t) • z₂) ∧
        (t : EReal) * w c z₁ + ((1 - t : ℝ) : EReal) * w c z₂ ≤ w c (t • z₁ + (1 - t) • z₂)) ∧
    (∀ c : Pt n, ∀ z ∈ I, f c z < ⊤ ∧ ⊥ < g c z ∧ 0 ≤ w c z) ∧
    ((intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty →
      ∀ c : Pt n, ((⨆ z ∈ IZ I ∩ intLattice d, w c z) < ⊤ ↔ (⨆ z ∈ IZ I, w c z) < ⊤)) := by sorry

end MICPRep.Periodic
