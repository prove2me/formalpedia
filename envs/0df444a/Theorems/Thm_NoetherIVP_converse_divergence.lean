-- Prove2me | Theorems.Thm_NoetherIVP_converse_divergence
-- name    : NoetherIVP.converse_divergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:58:24.818672+00:00
-- url     : https://prove2.me/theorems/745f1816-970d-4098-8d82-f573951dc695
-- title:
--   Noether (1918), §3: converse — a divergence relation forces invariance
-- statement:
--   **The converse direction of Theorem I (§3 of the paper).** Noether proves the converse by running
--   the argument of §2 backwards: from a divergence relation
--   $\sum_i \psi_i\,\delta u_i = \operatorname{Div} B$ one obtains, via the central identity (3), the
--   relation $\delta f + \operatorname{Div}(A - B) = 0$, "so if we put
--   $\Delta x = \frac{1}{f}(A-B)$, we have thereby arrived at (11)" — the infinitesimal invariance of
--   $I$ under the transformation determined by that $\Delta x$ and the given $\delta u$.
--
--   Formally: if $f[u]$ is nowhere zero and $\sum_i \psi_i[u](x)\,\delta u(x)_i = \operatorname{Div}B(x)$,
--   then with $\Delta x_l = (A_l - B_l)/f[u]$ the invariance identity (11) holds at $x$.
-- source:
--   E. Noether, Invariante Variationsprobleme (1918), Tavel translation, arXiv:physics/0503066v3, §3, p. 6, first paragraph (converse in the case of a finite group; Delta x = (A-B)/f).

import Mathlib
import Definitions.Def_NoetherIVP_core

namespace NoetherIVP
theorem converse_divergence {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (B : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x)
    (hB : ∀ l : Fin n, DifferentiableAt ℝ (fun y => B y l) x)
    (hf : ∀ y : Fin n → ℝ, lagr f u y ≠ 0)
    (hdiv : ∑ i : Fin m, lagrangeExpr f u i x * du x i = divg B x) :
    varF f u du x
        + divg (fun z l => lagr f u z * ((bdryA f u du z l - B z l) / lagr f u z)) x
      = 0 := by sorry
end NoetherIVP
