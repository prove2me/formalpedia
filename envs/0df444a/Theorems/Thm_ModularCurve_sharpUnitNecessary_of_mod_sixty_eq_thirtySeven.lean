-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirtySeven
-- name    : ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/6dbf5e5d-c6dc-5a7a-8144-a9abf6d40d52
-- title:
--   Necessity of n∣ m at levels ℓ≡ 37(mod 60)
-- statement:
--   For every natural number $i$, the predicate [`ModularCurve.SharpUnitNecessary`](def/ModularCurve_EtaQuotient.html#L100) holds at the level $\ell = 60i+37$. Unfolded, this asserts: for every natural number $m$ and every function $H : \mathfrak{H} \to \mathbb{C}$ on the upper half-plane such that $m > 0$, $H$ is continuous, the identity $$H(\tau)^{\ell-1} = \left(\frac{\Delta(\tau)}{\Delta(\gamma_\ell \cdot \tau)}\right)^{m}$$ holds for all $\tau \in \mathfrak{H}$, where $\Delta$ is `ModularForm.discriminant` and $\gamma_\ell$ is [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21) $\ell$, the element of $\mathrm{GL}_2(\mathbb{R})$ with upper triangular shape determined by $\ell$ (so that $\gamma_\ell$ acts as $\tau \mapsto \ell\tau$), and such that $H(\gamma \cdot \tau) = H(\tau)$ for all $\gamma$ in $\Gamma_0(\ell)$ and all $\tau$, one has $$\frac{\ell-1}{\gcd(\ell-1,12)} \;\Big|\; m,$$ the left side being [`ModularCurve.eisensteinNumerator`](def/ModularCurve_ModularUnit.html#L169) $\ell$ (here $\ell-1$ and the exponent $\ell-1$ are truncated natural subtraction). No primality is assumed: the assertion covers every member of the arithmetic progression $37, 97, 157, \dots$, composite levels included.
--
--   This is the necessity half of the statement that an $\ell$-th root situation for the $\eta$-quotient $\Delta(\tau)/\Delta(\ell\tau)$ forces $m$ to be divisible by the Eisenstein numerator $(\ell-1)/\gcd(\ell-1,12)$, i.e. the usual lower bound on the order of the modular unit attached to $\Gamma_0(\ell)$, established here uniformly along the residue class $\ell \equiv 37 \pmod{60}$. It feeds the class-by-class assembly of that necessity statement, being used in [`ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirtySeven.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven (i : ℕ) : ModularCurve.SharpUnitNecessary (60 * i + 37) := by sorry
