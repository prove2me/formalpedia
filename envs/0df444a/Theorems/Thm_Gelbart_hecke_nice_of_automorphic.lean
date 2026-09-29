-- Prove2me | Theorems.Thm_Gelbart_hecke_nice_of_automorphic
-- name    : Gelbart.hecke_nice_of_automorphic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:40:59.504882+00:00
-- url     : https://prove2.me/theorems/f20a1dc6-bed7-4510-88f0-3fc6c41d8c8d
-- title:
--   Theorem 1 (Hecke), (B) ⟹ (A)
-- statement:
--   The forward half of Hecke's Theorem 1. Let $a_n = O(n^{c})$ with $c > 0$, let $h, k > 0$ and $C = \pm 1$. If $$f(-1/z) = C\left(\frac{z}{i}\right)^{k} f(z) \qquad (\operatorname{Im} z > 0),$$ then $\Phi(s) + a_0/s + C a_0/(k-s)$ extends to an entire function, bounded in every vertical strip, satisfying the functional equation $F(k-s) = C F(s)$; equivalently $\Phi(k-s) = C\Phi(s)$.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, p. 188, §II.B.2, Theorem 1 (Hecke), direction (B) => (A)

import Definitions.Def_Gelbart_hecke_conditions

namespace Gelbart

theorem hecke_nice_of_automorphic
    (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ)
    (hc : 0 < c) (hh : 0 < h) (hk : 0 < k) (hC : C = 1 ∨ C = -1)
    (hgrowth : HeckeCoeffGrowth a c) :
    HeckeAutomorphic a h k C → HeckeNice a h k C (c + 1) := by sorry

end Gelbart
