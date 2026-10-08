-- Prove2me | Theorems.Thm_NonsmoothQN_Secant_alt_binary_expansion_exists_unique
-- name    : NonsmoothQN.Secant.alt_binary_expansion_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:57.518004+00:00
-- url     : https://prove2.me/theorems/4d90e0b4-4779-4048-b98f-c7a6b13c62ff
-- title:
--   Theorem 5.2 (first sentence), pp. 152–153 — every $x>0$ has a unique canonical alternating binary expansion
-- statement:
--   Every real number $x>0$ has an alternating binary expansion
--   $$x=\sum_{j=0}^{m}(-1)^j\,2^{-a_j},\qquad m\in\{0,1,2,\dots\}\cup\{\infty\},\quad a_0<a_1<a_2<\cdots\ \text{integers},$$
--   which is canonical (if $1\le m<\infty$ then $a_m\ge a_{m-1}+2$). Moreover any two canonical alternating binary expansions of $x$ have the same length $m$ and the same exponents $a_0,\dots,a_m$.
--
--   This is the number-theoretic half of Theorem 5.2: the secant method on $|x|$ reads off exactly this expansion of its starting point.
--
--   **Formalization Note** As printed, the theorem asserts uniqueness among all alternating binary expansions, which is false: $1=2^0=2^1-2^0$ and $\tfrac12=2^{-1}=2^0-2^{-1}$, and in general a finite expansion can be lengthened by $2^{-a}=2^{-(a-1)}-2^{-a}$ whenever its last gap is at least $2$ (or $m=0$). Uniqueness holds among canonical expansions, and the canonical one is the expansion followed by the secant method (e.g. $3/4=2^0-2^{-2}$, with iterates $3/4\to-1/4\to0$). The statement is therefore made for canonical expansions.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 152–153, Theorem 5.2, first sentence (corrected: canonical expansions)

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic
import Definitions.Def_NonsmoothQN_Secant_Expansion

namespace NonsmoothQN.Secant

theorem alt_binary_expansion_exists_unique (x : ℝ) (hx : 0 < x) :
    (∃ (m : ℕ∞) (a : ℕ → ℤ), IsAltBinExpansion x m a ∧ IsCanonicalExpansion m a) ∧
    ∀ (m m' : ℕ∞) (a a' : ℕ → ℤ),
      IsAltBinExpansion x m a → IsCanonicalExpansion m a →
      IsAltBinExpansion x m' a' → IsCanonicalExpansion m' a' →
      m = m' ∧ ∀ j : ℕ, (j : ℕ∞) ≤ m → a j = a' j := by sorry

end NonsmoothQN.Secant
