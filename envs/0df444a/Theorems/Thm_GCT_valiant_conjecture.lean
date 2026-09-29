-- Prove2me | Theorems.Thm_GCT_valiant_conjecture
-- name    : GCT.valiant_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:28:03.568837+00:00
-- url     : https://prove2.me/theorems/1e29a8e4-5e31-4885-a065-d9360cfa46c6
-- title:
--   Valiant's conjecture: $\mathrm{dc}(\mathrm{perm}_m)$ grows superpolynomially
-- statement:
--   **Valiant's conjecture** ($\mathbf{VP}_{ws} \ne \mathbf{VNP}$): the determinantal complexity of the permanent grows faster than any polynomial in $m$, i.e. for every exponent $c$ there is an $m_0$ with $\mathrm{dc}(\mathrm{perm}_m) > m^c$ for all $m \ge m_0$. Equivalently, there is no polynomially bounded sequence $n(m)$ and affine linear functions $x_{ij}(y)$ with $\mathrm{perm}_m(Y) = \det_{n(m)}(x(Y))$. This is the conjecture that motivated the GCT program; it is implied by the flagship conjecture and is open, the best known lower bound being the quadratic bound of Mignon–Ressayre.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 15, Conjecture 1.2.4.2 (Valiant [Val79]); cf. J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 40, Conjecture 12.4.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem valiant_conjecture :
    ∀ c : ℕ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → m ^ c < dc m := by sorry

end GCT
