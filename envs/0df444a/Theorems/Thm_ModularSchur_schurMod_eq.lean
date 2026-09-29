-- Prove2me | Theorems.Thm_ModularSchur_schurMod_eq
-- name    : ModularSchur.schurMod_eq
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:53:14.262823+00:00
-- url     : https://prove2.me/theorems/4e3eb2a6-5407-4ed1-9208-6fbf6fe859a5
-- title:
--   Main closed form: $S_m(k,\ell) = m/\gcd(m,\ell-1) - 1$ for $k \ge n-1$
-- statement:
--   This is the mission's headline result: a single closed form for the modular Schur number, valid at every modulus in the many-colours regime.
--
--   Throughout, $m \ge 2$ is the modulus, $\ell \ge 2$ the number of summands, $k \ge 1$ the number of colour classes, $d = \gcd(m, \ell - 1)$ and $n = m/d$.
--
--   For every $m \ge 2$, every $\ell \ge 2$, and every $k \ge n - 1$,
--
--   $$ S_m(k,\ell) = \frac{m}{\gcd(m, \ell - 1)} - 1. $$
--
--   Here the number counts colourings of an actual integer interval: it is the largest $N$ for which $[1,N]$ splits into at most $k$ classes, none of which contains $\ell$ elements summing to a member of the same class modulo $m$.
--
--   The formula is *closed* in a strong sense: it produces the value from $m$ and $\ell$ in a fixed number of elementary steps, one gcd, one division and one subtraction, with no search over colourings, no recursion, and no case split on $\ell \bmod m$. Earlier work in the literature settled individual small moduli by case analysis; this single identity covers every modulus at once in the stated range of $k$.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Theorem 1.2 (main closed form), integer level. Prior art: the paper states that the formula follows from [DSWH2025, Theorem 4 + Corollary 3] by choosing the optimal singleton, extending their coprime case (their Corollary 5) to every gcd and settling the large-$k$ regime of their Problem 1, part 5; see D'orville, Sim, Wong and Ho, "Modular generalizations of Schur numbers", Integers 25 (2025) #A62, https://math.colgate.edu/~integers/z62/z62.pdf. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/IntegerBridge.lean#L189-L193

import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset
variable {m : ℕ}

theorem ModularSchur.schurMod_eq (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    schurMod m k ℓ = m / Nat.gcd m (ℓ - 1) - 1 := by sorry
