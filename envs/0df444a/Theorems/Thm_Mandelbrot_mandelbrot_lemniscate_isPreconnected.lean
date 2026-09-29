-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_isPreconnected
-- name    : Mandelbrot.mandelbrot_lemniscate_isPreconnected
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T21:44:17.094164+00:00
-- url     : https://prove2.me/theorems/6d2bdeab-ecea-49a1-b49e-d848147d81f9
-- title:
--   The Mandelbrot lemniscate domains $M_k=\\{c : |p_k(c)| \\le 2\\}$ are connected
-- statement:
--   For $c \in \mathbb{C}$ write $f_c(z) = z^2 + c$ and let
--
--   $$p_k(c) \;=\; f_c^{\,k}(0)$$
--
--   be the $k$-th point of the critical orbit, a monic-up-to-scale polynomial in $c$ of degree $2^{k-1}$ for $k \ge 1$ (with $p_0 \equiv 0$). The **$k$-th Mandelbrot lemniscate domain** is the filled sublevel set
--
--   $$M_k \;=\; \{\, c \in \mathbb{C} : |p_k(c)| \le 2 \,\}.$$
--
--   The claim is that $M_k$ is connected for every $k$.
--
--   These sets are the standard finite-time approximations of the Mandelbrot set: they decrease, $M_0 \supseteq M_1 \supseteq \cdots$, and by the radius-$2$ escape criterion their intersection is exactly $M$. The first few are transparent: $M_0 = \mathbb{C}$ and $M_1$ is the closed disk of radius $2$, while for $k \ge 2$ the set $M_k$ is bounded by the lemniscate $|p_k(c)| = 2$, a curve of degree $2^{k-1}$.
--
--   Connectivity of a filled sublevel set $\{|p| \le R\}$ of a complex polynomial is governed by the critical values of $p$: the components of $\{|p| < R\}$ merge as $R$ grows past the moduli of the critical values, and the sublevel set is connected once $R$ dominates all of them. For the Mandelbrot polynomials the relevant fact is that every critical value of $p_k$ has modulus at most $2$, so no splitting occurs at level $2$. Equivalently, in the language of Douady and Hubbard, the Green's function of $M_k$ has no critical point in the region $\{|p_k| > 2\}$, which is the analytic heart of their proof that $M$ is connected.
--
--   Connectedness is stated in the preconnected form, which for these nonempty sets is equivalent to connectedness.
-- source:
--   A. Douady and J. H. Hubbard, Étude dynamique des polynômes complexes (Orsay notes), 1984/85, Exposé VIII (connectivity of M via the lemniscates |p_k| = 2); see also J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton Univ. Press 2006, Section 17 and Appendix (the Douady-Hubbard proof that M is connected).

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The `k`-th Mandelbrot lemniscate domain, the set of parameters whose critical orbit has
not yet left the closed disk of radius `2` at time `k`, is connected. -/
theorem mandelbrot_lemniscate_isPreconnected (k : ℕ) :
    IsPreconnected {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by sorry

end Mandelbrot
