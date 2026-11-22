-- Prove2me | Theorems.Thm_GRH_grh_implies_psiAP_square_root
-- name    : GRH.grh_implies_psiAP_square_root
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-21T14:18:02.251745+00:00
-- url     : https://prove2.me/theorems/087efb29-f7e5-4d6a-9c1a-8704147a5148
-- title:
--   Effective PNT for $\psi$ in arithmetic progressions under GRH
-- statement:
--   Assume the generalized Riemann hypothesis in the zero-free form used in this mission: for every modulus $q \ge 1$, every Dirichlet character $\chi \bmod q$ and every complex $s$ with $\Re(s) > 1/2$, the Dirichlet $L$-function $L(s,\chi)$ does not vanish, apart from the pole of the principal character at $s = 1$. Fix a modulus $q \ge 1$ and an integer $a$ with $\gcd(a,q) = 1$. Then there exists a constant $C \ge 0$ such that for every real $x \ge 2$, $$\bigl|\psi(x;q,a) - \tfrac{x}{\varphi(q)}\bigr| \;\le\; C\,\sqrt{x}\,(\log x)^2,$$ where $\psi(x;q,a) = \sum_{n \le x,\ n \equiv a \ ({\rm mod}\ q)} \Lambda(n)$ is the Chebyshev function restricted to the residue class $a \bmod q$. In other words, under GRH the von Mangoldt mass in a reduced residue class equals $x/\varphi(q)$ up to a square-root-scale error times a logarithmic factor; this is the $\psi$-form of the effective prime number theorem in arithmetic progressions under GRH.
-- source:
--   Decomposition of the prove2.me node GRH.grh_implies_primeCountingAP (GRH mission); effective prime number theorem in arithmetic progressions under the generalized Riemann hypothesis.

import Mathlib
import Definitions.Def_ArtinBV

namespace GRH

/-- **Effective prime number theorem for $\psi$ in arithmetic progressions under GRH.**
Assume the generalized Riemann hypothesis in the mission's zero-free form: $L(s,\chi)\ne 0$
whenever $\Re(s)>1/2$, for every modulus $q\ge 1$ and every Dirichlet character $\chi$ modulo $q$,
except the principal-character pole at $s=1$. Fix $q\ge1$, $a$ with $\gcd(a,q)=1$. Then there is a
constant $C\ge0$ such that for every real $x\ge2$,
$$\bigl|\psi(x;q,a)-\tfrac{x}{\varphi(q)}\bigr|\;\le\;C\,\sqrt{x}\,(\log x)^2,$$
where $\psi(x;q,a)=\sum_{n\le x,\ n\equiv a\ (q)}\Lambda(n)$ is `ArtinPrimitiveRoots.psiAP ⌊x⌋₊ q a`.

This is the Chebyshev-function form of the effective Dirichlet prime number theorem under GRH;
partial summation turns it into $\pi(x;q,a)=\mathrm{Li}(x)/\varphi(q)+O(x^{1/2+\varepsilon})$. -/
theorem grh_implies_psiAP_square_root
    (hGRH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (1 / 2 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0)
    (q a : ℕ) (hq : q ≠ 0) (ha : a.Coprime q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      |ArtinPrimitiveRoots.psiAP ⌊x⌋₊ q a - x / (q.totient : ℝ)| ≤
        C * x ^ ((1 : ℝ) / 2) * (Real.log x) ^ 2 := by sorry

end GRH
