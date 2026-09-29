-- Prove2me | Theorems.Thm_ModularSchur_unsafe_witness_residue
-- name    : ModularSchur.unsafe_witness_residue
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:48:42.93589+00:00
-- url     : https://prove2.me/theorems/e218d75a-2bd4-4d36-a3a7-18b0fbc9fc6e
-- title:
--   The residue $n = m/\gcd(m,\ell-1)$ is the self-defeating value
-- statement:
--   This theorem exhibits the single residue that no colouring can accommodate, which is the engine of the upper bound.
--
--   Throughout, $m \ge 2$ is the modulus, $\ell \ge 2$ the number of summands, $k \ge 1$ the number of colour classes, $d = \gcd(m, \ell - 1)$ and $n = m/d$.
--
--   For $m \ge 2$ and $\ell \ge 2$, the residue $n = m/d$ satisfies
--
--   $$ (\ell - 1)\, n \equiv 0 \pmod m, \qquad \text{that is, } (\ell - 1)\, \overline{n} = 0 \text{ in } \mathbb{Z}/m. $$
--
--   Combined with the singleton safety criterion, this says the one-element class $\{\overline{n}\}$ is *not* $\ell$-sum-free: $\ell$ copies of $n$ sum back to $n$. The value defeats itself.
--
--   This is the sharpest possible such witness, because $n$ is the least positive residue with this property, and it is why the modular Schur number stops exactly one step below $n$ rather than at some coarser bound such as $m$.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, the key step of Theorem 3.1, the self-defeating value described in Section 3. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/UnifiedValue.lean#L23-L32

import Mathlib

open Finset Nat
variable {m ℓ : ℕ}

theorem ModularSchur.unsafe_witness_residue (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    ((ℓ : ZMod m) - 1) * ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) = 0 := by sorry
