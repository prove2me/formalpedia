-- Prove2me | Theorems.Thm_FreeSpencer_Supplement_theorem_4_6
-- name    : FreeSpencer.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:33:17.704243+00:00
-- url     : https://prove2.me/theorems/b985c535-8345-451f-b1e3-f7e9cad9e01b
-- title:
--   Theorem 4.6 — the occupancy form equals the value form
-- statement:
--   Let $D\ge1$, let $\widehat A_1,\dots,\widehat A_\ell$ be real symmetric $D\times D$ matrices with $\|\widehat A_i\|\le1$, let $H$ be a real symmetric $D\times D$ matrix, and let $C\succeq0$ be a real $\ell\times\ell$ covariance (not required to satisfy $C\preceq I$; $\eta_C$ may vanish on a proper subspace of $\mathbb R^D$). Let $\mathfrak r$ be any regularizer that is continuous and concave on the density set $\mathcal D_D=\{S\succeq0:\operatorname{Tr}S=1\}$, and let $f_{\mathfrak r}$ and $E_{\mathfrak r}$ be the soft maximum and occupancy form of (4.11). Then the occupancy form equals the value form:
--   $$E_{\mathfrak r}(H,C)=\inf_{Z\succ0}f_{\mathfrak r}\big(H+Z^{-1}+\eta_C(Z)\big),$$
--   and this common value is the greatest lower bound of the values $f_{\mathfrak r}(H+Z^{-1}+\eta_C(Z))$, $Z\succ0$.
--
--   This is the analogue of Lehner's formula for the free spectral edge: the maximum over densities (occupancies) equals an infimum over value parameters $Z$, the inequality $\le$ being weak duality.
--
--   **Formalization Note** The maximum and the infimum are `sSup`/`sInf` of images; the second conjunct (`IsGLB`) makes the equality independent of Lean's junk value for an unbounded set.
--
--   Differences from the source:
--   - encoding: "E(H, C) = inf" → equality of `sSup`/`sInf` together with `IsGLB` of the value set; reason: Lean's `sInf` is `0` on a set unbounded below, so the greatest-lower-bound clause states the real infimum the page means; it changes no instance.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 4.6, p.29; definitions (4.11), p.29; setting §2.1, pp.18–19

import Mathlib
import Definitions.Def_FreeSpencer_Supplement_occForm
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer.Supplement

open FreeSpencer

/-- **Theorem 4.6** (The occupancy form equals the value form), (4.12): for every covariance `C ⪰ 0` and
every continuous concave regularizer `𝔯` on the density set, `E_𝔯(H, C) = inf_{Z ≻ 0} f_𝔯(H + Z⁻¹ + η_C(Z))`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914
(held file sha256 e1c1ba14…), Theorem 4.6, p.29; definitions (4.11), p.29; standing setting §2.1, pp.18–19.

**Formalization Note** The `Âᵢ` are the paper's real symmetric contractions and `H` is real symmetric
(§2.1); `D ≥ 1` is `Nonempty ι`. `C` is only positive semidefinite (no `C ⪯ I`), and `η_C` may vanish on a
proper subspace. The regularizer is any function continuous and concave on the convex density set. The
second conjunct says the value is a genuine greatest lower bound of the value-form set, so the identity
does not rest on the `sInf` junk value. -/
theorem theorem_4_6 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ : ℕ}
    (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (hC : C.PosSemidef) (r : Matrix ι ι ℝ → ℝ)
    (hr_cont : ContinuousOn r {S | IsDensity S}) (hr_conc : ConcaveOn ℝ {S | IsDensity S} r) :
    occForm r Ah H C = valueForm r Ah H C ∧ IsGLB (valueSet r Ah H C) (occForm r Ah H C) := by sorry

end FreeSpencer.Supplement
