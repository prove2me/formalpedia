-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_riemann_extension
-- name    : LeblSCV.BallPolydisc.riemann_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:24:22.618007+00:00
-- url     : https://prove2.me/theorems/ba22645f-8977-48e6-b6b6-e5bf6dabcbcc
-- title:
--   Theorem 1.6.1 — Riemann extension theorem across a zero set
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain and $g \in \mathcal{O}(U)$ not identically zero, with zero set $N = g^{-1}(0)$. If $f \in \mathcal{O}(U \setminus N)$ is locally bounded in $U$ (bounded on $W \cap (U \setminus N)$ for some neighbourhood $W$ of each point of $U$), then there exists a unique $F \in \mathcal{O}(U)$ such that
--   $$F|_{U \setminus N} = f.$$
--
--   In several variables the zero set of a holomorphic function plays the role of an isolated point in the one-variable Riemann removable singularity theorem. The theorem is used repeatedly to extend holomorphic functions across thin sets, for instance in the study of injective maps (Theorem 1.6.6) and of analytic varieties.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; a domain is open, connected and nonempty; $\mathcal{O}(W)$ means `DifferentiableOn ℂ` on $W$ ($U \setminus N$ is open because $g$ is continuous on the open set $U$). $N$ is `g ⁻¹' {0}`, so $U \setminus N = \{ z \in U : g(z) \ne 0 \}$; "not identically zero" is `∃ z ∈ U, g z ≠ 0`. Functions are ambient, so uniqueness is stated as: every holomorphic $G$ on $U$ that agrees with $f$ on $U \setminus N$ agrees with $F$ on $U$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 40, Theorem 1.6.1

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsLocallyBoundedIn

namespace LeblSCV.BallPolydisc

/-- Theorem 1.6.1 (Riemann extension theorem; Lebl, p. 40). Let `U ⊆ ℂⁿ` be a domain and `g`
holomorphic on `U`, not identically zero, with zero set `N = g⁻¹(0)`. If `f` is holomorphic on
`U ∖ N` and locally bounded in `U`, there is a unique `F` holomorphic on `U` with
`F|_{U∖N} = f` (unique as a function on `U`). -/
theorem riemann_extension {n : ℕ} (U : Set (Fin n → ℂ)) (hUo : IsOpen U) (hUc : IsConnected U)
    (g : (Fin n → ℂ) → ℂ) (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0)
    (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (U \ g ⁻¹' {0}))
    (hfb : IsLocallyBoundedIn f U (g ⁻¹' {0})) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ g ⁻¹' {0}) ∧
      ∀ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G U → Set.EqOn G f (U \ g ⁻¹' {0}) →
        Set.EqOn G F U := by sorry

end LeblSCV.BallPolydisc
