-- Prove2me | Theorems.Thm_LeblSCV_Levi_hartogs_figure_extension
-- name    : LeblSCV.Levi.hartogs_figure_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:05:01.592291+00:00
-- url     : https://prove2.me/theorems/75db3287-a22c-4858-9587-e3167d8caa60
-- title:
--   Theorem 2.1.4 — holomorphic functions on a Hartogs figure extend to the polydisc
-- statement:
--   Let $(z, w) = (z_1, \dots, z_m, w_1, \dots, w_k) \in \mathbb{C}^m \times \mathbb{C}^k$ be coordinates and $0 < a, b < 1$. Let
--   $$H = \{ (z,w) \in \mathbb{D}^{m+k} : |z_\ell| > a,\ \ell = 1,\dots,m \} \cup \{ (z,w) \in \mathbb{D}^{m+k} : |w_\ell| < b,\ \ell = 1,\dots,k \}.$$
--   If $f$ is holomorphic on $H$, then there is a holomorphic $F$ on the unit polydisc $\mathbb{D}^{m+k}$ with $F = f$ on $H$.
--
--   This is the basic extension phenomenon of several complex variables: it shows that not every domain in $\mathbb{C}^n$, $n \ge 2$, is a domain of holomorphy, and it is the device the tomato can principle uses after a change of coordinates.
--
--   **Formalization Note.** Holomorphic is `DifferentiableOn ℂ` on the (open) set; functions are ambient on `(Fin m → ℂ) × (Fin k → ℂ)`. The statement is for all `m, k : ℕ`; when `m = 0` or `k = 0` the figure is the whole polydisc and the claim is immediate.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 49, Theorem 2.1.4

import Mathlib
import Definitions.Def_LeblSCV_Levi_unitPolydiscProd
import Definitions.Def_LeblSCV_Levi_hartogsFigure

namespace LeblSCV.Levi

/-- Theorem 2.1.4 (Lebl, p. 49): a holomorphic function on the Hartogs figure `H ⊆ 𝔻^{m+k}`,
`0 < a, b < 1`, extends holomorphically to the unit polydisc `𝔻^{m+k}`. -/
theorem hartogs_figure_extension {m k : ℕ} (a b : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) (f : (Fin m → ℂ) × (Fin k → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (hartogsFigure m k a b)) :
    ∃ F : (Fin m → ℂ) × (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F (unitPolydiscProd m k) ∧
      Set.EqOn F f (hartogsFigure m k a b) := by sorry

end LeblSCV.Levi
