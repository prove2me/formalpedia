-- Prove2me | Theorems.Thm_Gelbart_hecke_automorphic_of_nice
-- name    : Gelbart.hecke_automorphic_of_nice
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:45:37.161379+00:00
-- url     : https://prove2.me/theorems/b0a22853-104e-4253-9f52-fe112041accb
-- title:
--   Theorem 1 (Hecke), (A) ⟹ (B)
-- statement:
--   The converse half of Hecke's Theorem 1, obtained by Mellin inversion ($"$to reverse the process and derive the functional equation, i.e. automorphy condition of $\theta(z)$ from that of $\zeta(s)$, we require Mellin inversion$"$, p. 188). Let $a_n = O(n^{c})$ with $c > 0$, $h, k > 0$ and $C = \pm 1$. If $\Phi(s) + a_0/s + C a_0/(k-s)$ extends to an entire function bounded in every vertical strip and satisfying $F(k-s) = C F(s)$, then $f(-1/z) = C (z/i)^{k} f(z)$ throughout the upper half-plane.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, p. 188, §II.B.2, Theorem 1 (Hecke), direction (A) => (B)

import Definitions.Def_Gelbart_hecke_conditions

namespace Gelbart

theorem hecke_automorphic_of_nice
    (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ)
    (hc : 0 < c) (hh : 0 < h) (hk : 0 < k) (hC : C = 1 ∨ C = -1)
    (hgrowth : HeckeCoeffGrowth a c) :
    HeckeNice a h k C (c + 1) → HeckeAutomorphic a h k C := by sorry

end Gelbart
