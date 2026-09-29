-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitNecessary_of_witness
-- name    : ModularCurve.sharpUnitNecessary_of_witness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/45983977-744c-5b39-9871-ad6689cfef0d
-- title:
--   Divisibility by the Eisenstein numerator from one Γ₀(ℓ) witness
-- statement:
--   Let $\ell$ be a nonzero natural number with $\ell \ge 2$, let $a, d$ be integers, let $c'$ be a positive natural number with $ad \equiv 1 \pmod{\ell c'}$, and let $z_0$ be an integer such that
--   $$12\Bigl(\frac{(a+d)(1-\ell)}{12\,\ell c'} + s(d, c') - s(d, \ell c')\Bigr) = \gcd(\ell-1, 12)\cdot z_0$$
--   as an identity in $\mathbb{Q}$, where $s(h,k) = \sum_{r=0}^{k-1} ((r/k))\,((hr/k))$ is the Dedekind sum formed with the sawtooth function [`dedekindSaw`](def/NumberTheory_DedekindSum.html#L11), which sends $x$ to $0$ when its fractional part vanishes and to $\{x\} - 1/2$ otherwise. Assume further that $|z_0|$ is coprime to $n := (\ell-1)/\gcd(\ell-1,12)$, the value of [`ModularCurve.eisensteinNumerator ℓ`](def/ModularCurve_ModularUnit.html#L169). Then [`ModularCurve.SharpUnitNecessary ℓ`](def/ModularCurve_EtaQuotient.html#L100) holds, that is: for every positive natural number $m$ and every continuous $H : \mathfrak{H} \to \mathbb{C}$ satisfying $H(\tau)^{\ell-1} = \bigl(\Delta(\tau)/\Delta(\ell\tau)\bigr)^m$ for all $\tau$ (with $\ell\tau$ given by the action of [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21)) and $H(\gamma\tau) = H(\tau)$ for all $\gamma \in \Gamma_0(\ell)$ and all $\tau$, one has $n \mid m$. Here $\ell - 1$ is natural subtraction.
--
--   This is the necessity half of the statement that the $\ell$-th power of an $\eta$-quotient modular unit on $X_0(\ell)$ has order divisible by the Eisenstein numerator $n = (\ell-1)/\gcd(\ell-1,12)$: a single matrix $\binom{a\ \ *}{\ell c'\ d} \in \Gamma_0(\ell)$ whose Rademacher $\Phi$-difference, normalised by $\gcd(\ell-1,12)$, is coprime to $n$ suffices to force the divisibility. It is the engine behind the congruence-class criteria [`ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_eleven`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_eleven), [`ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirteen`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirteen) and [`ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven), which instantiate the witness explicitly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitNecessary_of_witness.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitNecessary_of_witness (ℓ : ℕ) [NeZero ℓ] (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c') (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) (z₀ : ℤ) (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀) (hcop : Nat.Coprime z₀.natAbs (ModularCurve.eisensteinNumerator ℓ)) : ModularCurve.SharpUnitNecessary ℓ := by sorry
