-- Prove2me | Theorems.Thm_ModularCurve_PDPairing_pairZ_nondegenerate_mod
-- name    : ModularCurve.PDPairing.pairZ_nondegenerate_mod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/c7ad50ee-ee7a-51bb-aee6-ffc6790b1763
-- title:
--   Non-degeneracy of pairZ modulo a prime p≥ 5
-- statement:
--   Fix a natural number $N$ which is nonzero, and assume (as a typeclass hypothesis) that the congruence subgroup $\Gamma(4) \le \mathrm{SL}_2(\mathbb{Z})$ is a free group. Let $p$ be a natural number which is prime and satisfies $5 \le p$. The module in play is `parabolicHoms ℤ (Gamma0 N) ℤ`, the $\mathbb{Z}$-submodule of those additive homomorphisms $\varphi : \mathrm{Additive}\,\Gamma_0(N) \to \mathbb{Z}$ that vanish on every $\gamma \in \Gamma_0(N)$ whose matrix satisfies $(\mathrm{tr}\,\gamma)^2 = 4$, and on it one has the $\mathbb{Z}$-bilinear form [`ModularCurve.PDPairing.pairZ N`](def/ModularCurve_PDPairing.html#L654), built from `pairZFun N`: the value on $\varphi, \psi$ is the integer $48$ divided (in natural-number division) by the relative index of $\Gamma_0(N) \cap \Gamma(4)$ in $\Gamma_0(N)$, times the cusp sum over $\Gamma_0(N) \cap \Gamma(4)$ of `hPrim` applied to the restrictions of $\varphi$ and $\psi$ to that intersection. The conclusion is a conjunction of two divisibility statements, one for each slot: first, every $x$ such that $p \mid \mathrm{pairZ}\,N\,x\,y$ for all $y$ is of the form $x = p \cdot x'$ for some $x'$ in the same module; second, every $y$ such that $p \mid \mathrm{pairZ}\,N\,x\,y$ for all $x$ is of the form $y = p \cdot y'$.
--
--   This is the non-degeneracy modulo $p$ of the integral Poincaré duality pairing on parabolic homomorphisms of $\Gamma_0(N)$, stated in divisibility form so as to avoid reduction maps; the restriction $p \ge 5$ reflects the factor $48$ (and the $2$- and $3$-torsion it absorbs) in the normalisation of the pairing. It feeds the construction of a perfect self-adjoint pairing on `parabolicHoms` compatible with degeneracy maps, and the study of the $q$-new support of normalised eigenforms at odd primes in the level-raising argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PDPairing_pairZ_nondegenerate_mod.lean

import Definitions.Def_ModularCurve_PDPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularCurve.Period in

theorem ModularCurve.PDPairing.pairZ_nondegenerate_mod (N : ℕ) [NeZero N] [IsFreeGroup ↥(Gamma 4)]
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x') ∧
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ y' : parabolicHoms ℤ (Gamma0 N) ℤ, y = (p : ℤ) • y') := by sorry
